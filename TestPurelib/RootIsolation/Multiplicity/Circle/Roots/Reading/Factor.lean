module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Factor
import Purelib.RootIsolation.Multiplicity.Circle.Inventory
import Purelib.Polynomial.Clearance.Circle
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Actual paid factor dispatch from original mixed multiplicities

The same original inventory of a double zero and a triple exterior linear
root supplies both observations, locations and arguments. Each observation
constructs an actual paid formal tower reading using its retained physical
bounds; the independently expected quadrances are zero and four.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Factor

open Purelib
open Data.Gaussian
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Clearance.Circle (Certificate Margin)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Roots (Tower)
open Polynomial.Dense.Roots.Tower.Reading (Parameters Request)
open Algebra.Ring (GaussianReading)
open RationalFunctions.Curve.Canonical.Circle
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots.Reading (Bounds)
open RootIsolation.Multiplicity.Circle.Roots

/-- The original mixed source has a double zero and a triple exterior root at two. -/
private def source : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- Each retained original factor constructs its actual selected formal association once. -/
private def check {opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : IO Unit := do
  let mut rows := []
  for index in List.ofFn (fun index : Fin input.contexts.length => index) do
    let context := input.contexts.get index
    let factor := inventory.factorAt index
    let argument := ObservationArgument.prepare factor.observation factor.locations
    let bounds := Bounds.prepare factor.observation factor.locations argument
    let polynomial := context.focus.part.polynomial
    let tower := Tower.prepare polynomial context.focus.part.normalized polynomial.leadingCoeff⁻¹
      (Canonical.mul_inv_cancel _ (DensePolynomial.leadingCoeff_ne_zero context.focus.part.nonzero))
    let parameters := Parameters.prepare tower Norm.weight GaussianReading.identity.gain bounds.radius
      GaussianReading.identity.gainNonnegative bounds.radius_nonnegative
    let request := Request.prepare parameters 1 (by decide +kernel)
    have leading : Tower.Leading tower id polynomial.leadingCoeff :=
      Tower.Leading.ofSource tower id polynomial.leadingCoeff context.focus.part.normalized rfl
        rfl rfl (fun _ _ => rfl)
    have sourceEq : polynomial = Map.map GaussianReading.identity.read polynomial := (Map.map_id polynomial).symm
    let retained := Reading.Factor.prepare factor.observation factor.locations argument bounds request.budget leading
      GaussianReading.identity rfl sourceEq rfl (Purelib.Data.Rat.Fraction.Order.Basic.le_refl _)
    for rootIndex in List.ofFn (fun rootIndex : Fin tower.blocks.length => rootIndex) do
      let point := retained.realization.finalReading.read (tower.blocks[rootIndex.val]'rootIndex.isLt).point
      let inside := Locations.insideAt factor.observation factor.locations (Reading.Factor.localIndex rfl rootIndex)
      have _ := Reading.Factor.inside retained rfl rootIndex
      have _ := Reading.Factor.outside retained rfl rootIndex
      have _ := Reading.Factor.error_lt retained request.budget.tolerance_positive
      unless (if inside then point.normSq ≤ bounds.ceiling else bounds.floor ≤ point.normSq) &&
          retained.realization.finalReading.error < 1 do
        throw (IO.userError "the actual selected root reading lost its original radial bound or paid error")
      rows := rows ++ [(index.val, context.focus.multiplicity, inside, point.normSq, bounds.ceiling, bounds.floor)]
  unless rows == [(0, 3, false, 4, 4, 4), (1, 2, true, 0, 0, 0)] do
    throw (IO.userError "the original exact factor dispatch changed its independently expected root quadrances")
  System.IO.println "Original factor dispatch: exterior triple root norm4, interior double zero norm0; paid errors<1."

/-- Consume the same already materialized original positive radial inventory. -/
private def positive {clearance : Certificate source} (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "the mixed dispatch fixture became constant")
  | .positive _ _, locations => check locations

/-- Build the mixed original inventory and dispatch each same retained observation into its actual formal reading. -/
public def run : IO Unit := do
  let attempt := Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the mixed dispatch fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "the mixed dispatch fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive (Inventory.prepare margin.toCertificate (by decide +kernel))

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Factor
