module

import TestPurelib.Polynomial.Laurent.Toeplitz
import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Recovery
import Purelib.Data.Vector.Split
import Purelib.System.IO

/-!
# Actual public Laurent–Toeplitz recovery after mixed-mode cancellation

The original public comparison retains one inside root and a repeated
outside root. Its full characteristic basis recovers independently chosen
initial values before any late-window request or common reading is made.
One actual paid window gives an obstruction from physical coefficient
evidence. A second request on the same ledger retains the inconclusive
outcome for an entirely zero observed combination.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Recovery

open Purelib
open Data renaming Vector → Vec
open Data.Vector.Basic
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Data.Rat.Fraction (Rational)
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open Polynomial.Laurent.Toeplitz (Comparison)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.Multiplicity.Side.Basic (SideResult)
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots.Recurrence.Recovery
open RationalFunctions.Curve.Canonical.Circle
open LinearAlgebra.Matrix

/-- The original Laurent symbol is the shifted product of one inside and two equal outside factors. -/
private def source : LaurentPolynomial :=
  ⟨[⟨1, .nonnegative 2⟩, ⟨-(9 / 2), .nonnegative 1⟩,
    ⟨6, .nonnegative 0⟩, ⟨-2, .negative 0⟩]⟩

/-- Check the original full basis against mixed initial values with genuine cancellation at zero. -/
private def positive {polynomial opposite : CoefficientPolynomial}
    {input : PositiveSideInput polynomial opposite} {clearance : Certificate polynomial}
    {family : PositiveFamily input} {inventory : PositiveInventory clearance input family}
    {argument : PositiveArgument inventory} {rows : Nat}
    (retained : Roots.Recurrence argument rows) : IO Unit := do
  let embedding := Images.coefficientMap retained.prepared.separation.prepared.stages
  if fullCount : retained.recurrence.fullWord.length = 3 then
    let initial : Vec retained.prepared.separation.Scalar retained.recurrence.fullWord.length :=
      fullCount.symm ▸ .cons (embedding 0) (.cons (embedding (-(1 / 2))) (.cons (embedding (1 / 4)) .nil))
    let coefficients := retained.recurrence.basis.coordinates initial
    let restored := Rectangular.apply retained.recurrence.basis.matrix coefficients
    for column in List.ofFn (fun column : Fin retained.recurrence.fullWord.length => column) do
      let root := retained.prepared.bank.block (retained.recurrence.fullWord[column.val]'column.isLt)
      let order := retained.recurrence.basis.occurrences.orders column
      let expected : Canonical := if root.point = embedding (1 / 2) then 1 else if order = 0 then -1 else 1
      unless decide (restored column = initial column) && decide (coefficients column = embedding expected) do
        throw (IO.userError "the original full basis lost the independent mixed-mode coefficients")
      if root.point = embedding (1 / 2) then
        unless order == 0 do
          throw (IO.userError "the original inside factor acquired a repeated occurrence")
      else
        unless decide (root.point = embedding 2) && order < 2 do
          throw (IO.userError "the original repeated outside factor changed its point or occurrence order")
    let lower : Rational := 1 / 2
    let target : Rational := 1 / 4
    System.IO.println "Public recovery: full mixed coefficients and physical thresholds fixed; preparing requests."
    let request := Request.prepare retained coefficients lower (by decide +kernel) target (by decide +kernel)
    let zeroCoefficients := vectorOfFn (fun _ : Fin retained.recurrence.fullWord.length =>
      (0 : retained.prepared.separation.Scalar))
    let zeroRequest := Request.prepare retained zeroCoefficients (1 : Rational) (by decide +kernel)
      target (by decide +kernel)
    have _ := request.restore
    have _ := zeroRequest.restore
    have _ := retained.recurrence.horizon_satisfies
      (request.schedule.start + retained.recurrence.fullWord.length) coefficients
    unless decide (0 < request.schedule.tolerance) && decide (0 < zeroRequest.schedule.tolerance) &&
        decide (1 < request.outside.commonFloor) do
      throw (IO.userError "the pre-observation recovery requests lost their positive paid tolerances")
    System.IO.println s!"Public recovery: mixed and zero requests fixed before observation; \
      mixed-start{request.schedule.start}, zero-start{zeroRequest.schedule.start}."
    let observation := Observation.prepare request
    let zeroObservation := Observation.prepare zeroRequest
    have _ := observation.restore
    have _ := zeroObservation.restore
    have _ := observation.gain_eq
    have _ := observation.error_le
    have _ := zeroObservation.error_le
    unless observation.reading.gain == retained.parameters.finalGain &&
        decide (observation.reading.error ≤ request.schedule.tolerance) &&
        decide (zeroObservation.reading.error ≤ zeroRequest.schedule.tolerance) do
      throw (IO.userError "the same original recovery associations did not pay their retained requests")
    let first : Fin retained.recurrence.fullWord.length := ⟨0, fullCount.symm ▸ (by decide)⟩
    unless decide (observation.reading.read (initial first) = 0) do
      throw (IO.userError "the mixed original combination lost its actual physical initial cancellation")
    let mut queried := 0
    for column in List.ofFn (fun column : Fin retained.recurrence.fullWord.length => column) do
      let tag := retained.recurrence.fullWord[column.val]'column.isLt
      let root := retained.prepared.bank.block tag
      let order := retained.recurrence.basis.occurrences.orders column
      let expected : Canonical := if root.point = embedding (1 / 2) then 1 else if order = 0 then -1 else 1
      have _ := observation.observed.coefficientValues_eq column
      unless decide (observation.observed.coefficientValues column = expected) &&
          decide (zeroObservation.observed.coefficientValues column = 0) do
        throw (IO.userError "the actual common reading changed an original physical coefficient")
      if selected : request.outside.selected tag = true then
        queried := queried + 1
        have _ := observation.outside tag selected
        if evidence : lower ≤ Norm.Basic.normSq (observation.observed.coefficientValues column) then
          let witness := observation.obstruction column selected evidence
          let time := request.schedule.start + witness.val.val
          let value := observation.observed.values witness.val
          let independent : Canonical := (1 / 2 : Canonical) ^ time - (2 : Canonical) ^ time +
            if time = 0 then 0 else (time : Canonical) * (2 : Canonical) ^ (time - 1)
          unless decide (target < Norm.Basic.normSq value) && decide (value = independent) do
            throw (IO.userError "the actual paid recovery failed its concrete independent late-window obstruction")
          System.IO.println s!"Public recovery: outside-order{order}, physical-coefficient-norm1, \
            index{witness.val.val}, time{time}; actual mixed value exceeds quadrance1/4."
        else
          throw (IO.userError "the original nonzero mixed physical coefficient failed its requested lower bound")
        if zeroSelected : zeroRequest.outside.selected tag = true then
          match zeroObservation.check column zeroSelected with
          | .obstruction _ _ => throw (IO.userError "the zero observed combination acquired a large late coordinate")
          | .inconclusive allSmall coefficientSmall =>
              have _ := coefficientSmall
              for index in List.ofFn (fun index : Fin retained.recurrence.fullWord.length => index) do
                have _ := allSmall index
                unless decide (zeroObservation.observed.values index = 0) &&
                    decide (Norm.Basic.normSq (zeroObservation.observed.values index) ≤ target) do
                  throw (IO.userError "the retained inconclusive outcome lost its actual zero window")
        else
          throw (IO.userError "the same-ledger zero request changed the original outside label")
    unless queried == 2 do
      throw (IO.userError "the actual public recovery did not inspect both repeated outside occurrences")
    System.IO.println "Public recovery: same-ledger zero request retained inconclusive physical evidence."
  else
    throw (IO.userError "the public recovery source lost its full three-column characteristic basis")

/-- Consume the actual positive public ledger without reconstructing its inventory, roots or basis. -/
private def ledger {polynomial opposite : CoefficientPolynomial} {clearance : Certificate polynomial}
    (rows : Nat) : (side : SideResult polynomial opposite) → (locations : SideLocations clearance side) →
      (argument : SideArgument side locations) → Recurrence.Side rows side locations argument → IO Unit
  | .constant _ _ _, _, _, _ => throw (IO.userError "the mixed recovery source became constant")
  | .positive _ _, _, _, retained => positive retained

/-- Prepare one actual original public comparison before either recovery request is observed. -/
public def run : IO Unit := do
  System.IO.println "Public recovery: constructing one actual original Laurent comparison and recurrence ledger."
  match source.prepare with
  | .zero _ => throw (IO.userError "the nonzero mixed recovery source became the zero symbol")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial 8
      match boundary.2 with
      | .contact _ _ _ => throw (IO.userError "the mixed recovery source met the unit circle")
      | .inconclusive _ _ _ _ _ => throw (IO.userError "the mixed recovery source lacked whole-circle clearance")
      | .clear clearance =>
          let result := Comparison.prepare normalized boundary.1.paths clearance
          have _ := result.restore
          unless normalized.poleOrder == 1 && result.circle.polynomial.inventory.insideCount == 1 &&
              result.circle.polynomial.inventory.outsideCount == 2 && result.index == 0 &&
              result.circle.reading.winding == 0 do
            throw (IO.userError "the actual mixed recovery comparison lost its pole, locations or index")
          TestPurelib.Polynomial.Laurent.Toeplitz.ledger normalized.poleOrder 1 0 0 0 false
            result.circle.polynomial.inventory.side result.circle.polynomial.inventory.locations
            result.circle.polynomial.argument result.recurrence
          ledger normalized.poleOrder result.circle.polynomial.inventory.side
            result.circle.polynomial.inventory.locations result.circle.polynomial.argument result.recurrence

end TestPurelib.Polynomial.Laurent.Toeplitz.Recovery
