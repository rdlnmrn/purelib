module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank
import Purelib.Polynomial.Clearance.Circle
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# The same automatic prepared Bank at its paid original root owners

A double zero and triple exterior linear root retain their original
preprocessing, formal Bank, geometric inventory, aligned owners and cached
physical bounds. Their original stage parameters are fixed before the
actual family reading is assembled in that same final coefficient algebra.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank

open Purelib
open Data.Gaussian
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading renaming Request → StageRequest
open Polynomial.Clearance.Circle (Certificate Margin)
open RationalFunctions.Curve.Canonical.Circle
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots

/-- The original mixed source has two focused factors with different positive multiplicities and radial sides. -/
private def source : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- Retain all original parents while constructing the requested actual common Bank reading. -/
private def check {opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : IO Unit := do
  let prepared := Polynomial.Dense.Gaussian.Multiplicity.Roots.prepare input
  let owners := Owners.prepare prepared inventory
  let argument := PositiveArgument.prepare inventory
  let bounds := Reading.Bounds.Family.prepare argument
  let parameters := Reading.Bank.prepareParameters prepared bounds
  let request := StageRequest.prepare parameters 1 (by decide +kernel)
  let retained := Reading.Bank.prepare prepared argument bounds request
  let reading := retained.model.finalReading
  have _ := retained.final_gain
  have _ := retained.error_lt
  have _ := retained.read_scalar (⟨3, 1⟩ : Canonical)
  let quadrances := List.ofFn (fun index : Fin prepared.bank.blocks.length =>
    (reading.read (prepared.bank.block index).point).normSq)
  let mut ownerRows := []
  for index in List.ofFn (fun index : Fin prepared.bank.blocks.length => index) do
    let occurrence := owners.occurrences index
    let physical := bounds.boundsAt occurrence.context
    let inside := occurrence.inside inventory
    let quadrance := (reading.read (prepared.bank.block index).point).normSq
    have _ := Reading.Bank.inside prepared owners retained index
    have _ := Reading.Bank.outside prepared owners retained index
    unless if inside then quadrance ≤ physical.ceiling else physical.floor ≤ quadrance do
      throw (IO.userError "the same prepared Bank block lost its original owner's quantitative radial bound")
    ownerRows := ownerRows ++ [(occurrence.context.val, occurrence.multiplicity, inside, quadrance)]
  unless ownerRows == [(0, 3, false, 4), (1, 2, true, 0)] do
    throw (IO.userError "the same prepared Bank lost an original context, multiplicity, label or root quadrance")
  unless prepared.bank.blocks.length == 2 && quadrances == [4, 0] && parameters.factors == 2 &&
      parameters.finalGain == 4 && reading.gain == 4 && reading.error == 0 &&
      owners.selection.count == 2 && inventory.insideCount == 2 && inventory.outsideCount == 3 &&
      reading.read (prepared.separation.prepared.stages.embed (⟨3, 1⟩ : Canonical)) == (⟨3, 1⟩ : Canonical) do
    throw (IO.userError "the same prepared Bank lost its paid common endpoint, roots, owners or exact scalar reading")
  System.IO.println "Same prepared Bank: two original blocks/owner bounds, \
    selected2, gain4/error0 and exact root norms4/0."

/-- Consume the same cached positive inventory and its original preprocessing. -/
private def positive {clearance : Certificate source} (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "the prepared Bank fixture became constant")
  | .positive _ _, locations => check locations

/-- Construct one original inventory and its same automatic Bank before paying the fixed model request. -/
public def run : IO Unit := do
  let attempt := Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the prepared Bank fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "the prepared Bank fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive (Inventory.prepare margin.toCertificate (by decide +kernel))

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank
