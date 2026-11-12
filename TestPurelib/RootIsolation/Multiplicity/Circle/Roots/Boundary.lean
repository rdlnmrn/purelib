module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Boundary
import Purelib.Polynomial.Clearance.Circle
import Purelib.System.IO

/-!
# Actual labelled boundaries from original radial inventories

A double zero supplies genuine nonunit-root transients at zero startup rows.
A nonmonic double interior root supplies a nontrivial original constant
reciprocal, an actual coupled startup row and its original kernel vector.
Both construction chains keep the original prepared bank and owner selection.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Boundary

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian.Multiplicity.Roots
open Polynomial.Clearance.Circle (Certificate Margin)
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots
open Data.Gaussian.Basic (Canonical)
open Data renaming Vector → Vec

/-- A genuine double zero retains both original zero-root transients. -/
private def zeroSource : CoefficientPolynomial := ⟨[1, 0, 0]⟩

/-- A nonmonic original quadratic has a repeated interior root and constant coefficient one half. -/
private def repeatedSource : CoefficientPolynomial := ⟨[2, -2, 1 / 2]⟩

/-- The same original source coefficient table is already normalized in both fixtures. -/
private theorem normalized : zeroSource.normalize = zeroSource ∧ repeatedSource.normalize = repeatedSource := by
  decide +kernel

/-- Positive startup rows can use the original repeated source's nonzero constant. -/
private theorem repeated_constant : repeatedSource.eval 0 ≠ 0 := by decide +kernel

/-- Actual prepared boundaries retain the complete same original owner selection. -/
private theorem same_selection {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input} {prepared : Prepared input}
    {inventory : PositiveInventory clearance input family} (owners : Owners prepared inventory)
    (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0) :
    (Roots.Boundary.prepare owners rows nonzero).selected.selection = owners.selection :=
  (Roots.Boundary.prepare owners rows nonzero).selection_eq

/-- Retaining the actual original caches restores the complete boundary with no new selection or boundary producer. -/
private theorem restore {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input} {prepared : Prepared input}
    {inventory : PositiveInventory clearance input family} (owners : Owners prepared inventory)
    (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0) :
    let boundary := Roots.Boundary.prepare owners rows nonzero
    Roots.Boundary.ofSelected owners rows boundary.constantNonzero boundary.constant boundary.constant_eq
        boundary.selected boundary.selected_eq = boundary :=
  Roots.Boundary.ofSelected_eq_prepare owners rows nonzero _ rfl _ rfl

/-- The original zero-row procedure cannot allocate a reciprocal or positive-shift transport. -/
private theorem zero_inverse_free {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input} {prepared : Prepared input}
    {inventory : PositiveInventory clearance input family} (owners : Owners prepared inventory) :
    (Roots.Boundary.prepare owners 0 (fun impossible => False.elim (Nat.not_lt_zero 0 impossible))).constant =
      .zero := rfl

/-- Check both actual nonunit-root transients in the original inverse-free boundary. -/
private def zero {opposite : CoefficientPolynomial} {input : PositiveSideInput zeroSource opposite}
    {clearance : Certificate zeroSource} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : IO Unit := do
  let prepared := Polynomial.Dense.Gaussian.Multiplicity.Roots.prepare input
  let owners := Owners.prepare prepared inventory
  let boundary := Roots.Boundary.prepare owners 0 (fun impossible => False.elim (Nat.not_lt_zero 0 impossible))
  let normal := boundary.selected.result.normal
  unless inventory.insideCount == 2 && owners.selection.count == 2 &&
      Roots.Boundary.horizon prepared 0 == 3 && normal.rank == 0 &&
      normal.kernelDimension == 2 && normal.cokernelDimension == 0 && normal.defect == -2 do
    throw (IO.userError "the original double-zero boundary lost its inverse-free transients")
  if columns : boundary.selected.selection.word.length = 2 then
    let first : Fin boundary.selected.selection.word.length := ⟨0, columns.symm ▸ (by decide)⟩
    let second : Fin boundary.selected.selection.word.length := ⟨1, columns.symm ▸ (by decide)⟩
    have room : Roots.Boundary.horizon prepared 0 = 3 := (Roots.Boundary.horizon_eq_source prepared 0).trans rfl
    let initial : Fin (Roots.Boundary.horizon prepared 0) := ⟨0, room.symm ▸ (by decide)⟩
    let next : Fin (Roots.Boundary.horizon prepared 0) := ⟨1, room.symm ▸ (by decide)⟩
    let values := boundary.selected.result.readings.values
    let embedding := Stages.Images.coefficientMap prepared.separation.prepared.stages
    unless decide (values first initial = embedding 1) &&
        decide (values first next = embedding 0) &&
        decide (values second initial = embedding 0) &&
        decide (values second next = embedding 1) do
      throw (IO.userError "the actual two original zero-root jets changed")
  else
    throw (IO.userError "the double-zero selection changed its original word length")
  System.IO.println "Original zero-root boundary: rows0, horizon3, kernel2, complement0, defect-2."

/-- Check the actual nonmonic repeated-root boundary and its original finite kernel coordinates. -/
private def repeated {opposite : CoefficientPolynomial} {input : PositiveSideInput repeatedSource opposite}
    {clearance : Certificate repeatedSource} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : IO Unit := do
  let prepared := Polynomial.Dense.Gaussian.Multiplicity.Roots.prepare input
  let owners := Owners.prepare prepared inventory
  let boundary := Roots.Boundary.prepare owners 1 (fun _ => repeated_constant)
  let normal := boundary.selected.result.normal
  unless inventory.insideCount == 2 && owners.selection.count == 2 &&
      Roots.Boundary.horizon prepared 1 == 4 && normal.rank == 1 &&
      normal.kernelDimension == 1 && normal.cokernelDimension == 0 && normal.defect == -1 do
    throw (IO.userError "the original repeated-root boundary lost its actual normal form")
  match boundary.constant with
  | .positive coefficientInverse _ inverse _ _ =>
      unless decide (coefficientInverse = 2) &&
          decide (inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages 2) do
        throw (IO.userError "the nonmonic original constant reciprocal or its same final image changed")
  if columns : boundary.selected.selection.word.length = 2 then
    let first : Fin boundary.selected.selection.word.length := ⟨0, columns.symm ▸ (by decide)⟩
    let second : Fin boundary.selected.selection.word.length := ⟨1, columns.symm ▸ (by decide)⟩
    let matrix := boundary.selected.result.boundary
    let embedding := Stages.Images.coefficientMap prepared.separation.prepared.stages
    unless decide (matrix 0 first = embedding (-1)) && decide (matrix 0 second = embedding 2) do
      throw (IO.userError "the actual original repeated-root startup row changed")
    if free : boundary.selected.selection.word.length - normal.rank = 1 then
      let coordinates : Vec prepared.separation.Scalar
          (boundary.selected.selection.word.length - normal.rank) := free.symm ▸ .cons (embedding 1) .nil
      let kernel := normal.kernelVector coordinates
      unless decide (kernel first = embedding 1) && decide (kernel second = embedding (1 / 2)) do
        throw (IO.userError "the original repeated-root kernel readback changed")
    else
      throw (IO.userError "the original repeated-root kernel dimension changed")
  else
    throw (IO.userError "the repeated-root selection changed its original word length")
  System.IO.println "Original repeated-root boundary: rows1, horizon4, row[-1,2], kernel[1,1/2], defect-1."

/-- Dispatch a retained original positive inventory without reconstructing its source parents. -/
private def positive {source : CoefficientPolynomial} {clearance : Certificate source}
    (check : {opposite : CoefficientPolynomial} → {input : PositiveSideInput source opposite} →
      {family : PositiveFamily input} → PositiveInventory clearance input family → IO Unit)
    (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "a positive boundary fixture became constant")
  | .positive _ _, locations => check locations

/-- Construct the original whole-circle inventory and feed its same actual bank and owner selection to the boundary. -/
private def exercise (source : CoefficientPolynomial) (sourceNormalized : source.normalize = source)
    (check : {clearance : Certificate source} → {opposite : CoefficientPolynomial} →
      {input : PositiveSideInput source opposite} → {family : PositiveFamily input} →
      PositiveInventory clearance input family → IO Unit) : IO Unit := do
  let attempt := RationalFunctions.Curve.Canonical.Circle.Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "an original boundary fixture met the unit circle")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "an original boundary fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive check (Inventory.prepare margin.toCertificate sourceNormalized)

/-- Execute the same original zero-root and nonmonic repeated-root labelled boundary construction chains. -/
public def run : IO Unit := do
  exercise zeroSource normalized.left zero
  exercise repeatedSource normalized.right repeated

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Boundary
