module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Family
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Origins
import Purelib.Polynomial.Clearance.Circle
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# One actual paid reading across original mixed factor owners

The original inventory of a double zero and triple exterior linear root
supplies one argument and bound family. The same automatic formal stage
chain consumes each actual preceding endpoint, ending in one common reading
with independently expected root quadrances four and zero.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Family

open Purelib
open Data.Gaussian
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian.Multiplicity.Roots (Stages)
open Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
open Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading renaming
  Parameters → StageParameters, Request → StageRequest
open Polynomial.Clearance.Circle (Certificate Margin)
open Algebra.Ring (GaussianReading)
open RationalFunctions.Curve.Canonical.Circle
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots

/-- The original source retains two distinct multiplicities and both strict radial sides. -/
private def source : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- Compose the same original formal towers against the same original inventory and cached physical bounds. -/
private def check {opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (prepared : Stages.Prepared input) : IO Unit := by
  rcases prepared with ⟨contexts, contextsEq, indices, indicesEq, stages⟩
  cases contextsEq
  exact do
    let argument := PositiveArgument.prepare inventory
    let bounds := Reading.Bounds.Family.prepare argument
    let parameters := StageParameters.prepare stages Norm.weight 1 bounds.radii (by decide +kernel)
      bounds.radii_nonnegative
    let request := StageRequest.prepare parameters 1 (by decide +kernel)
    have leading : Stages.Leading stages :=
      Stages.Leading.ofScalar stages rfl rfl (fun _ _ => rfl) (fun _ _ same => same)
    let retained := Reading.Family.prepare argument bounds leading request.budget GaussianReading.identity rfl
    let images := Images.prepare stages
    let blocks := Images.blocks stages images
    let readNorms := List.ofFn (fun index : Fin blocks.length =>
      (retained.model.finalReading.read (blocks.get index).point).normSq)
    let mut ownerRows := []
    for index in List.ofFn (fun index : Fin blocks.length => index) do
      let origin := Images.Origin.ofIndex stages images index
      let original := inventory.factorAt origin.contextIndex
      let physical := bounds.boundsAt origin.contextIndex
      let label := Locations.insideAt original.observation original.locations origin.localIndex
      let quadrance := (retained.model.finalReading.read origin.point).normSq
      have _ := retained.radial images origin
      have _ := retained.inside images origin
      have _ := retained.outside images origin
      unless if label then quadrance ≤ physical.ceiling else physical.floor ≤ quadrance do
        throw (IO.userError "an original factor-root owner lost its quantitative bound in the common endpoint")
      ownerRows := ownerRows ++ [(origin.contextIndex.val, label, quadrance)]
    unless ownerRows == [(0, false, 4), (1, true, 0)] do
      throw (IO.userError "the common endpoint changed an original context, label or root quadrance")
    have _ := retained.final_gain
    have _ := retained.error_lt request.positive
    have _ := retained.final_read_embed (⟨3, 1⟩ : Canonical)
    unless input.contexts.length == 2 && parameters.factors == 2 && blocks.length == 2 &&
        readNorms == [4, 0] && parameters.finalGain == 4 && retained.model.finalReading.gain == 4 &&
        retained.model.finalReading.error == 0 &&
        retained.model.finalReading.read (stages.embed (⟨3, 1⟩ : Canonical)) == (⟨3, 1⟩ : Canonical) do
      throw (IO.userError "the original factor family lost its shared endpoint, exact coefficients or root quadrances")
    System.IO.println "Original factor family: two actual chained payloads, common gain4/error0, \
      original owner bounds and norms4/0."

/-- Consume the same already materialized original positive inventory before preparing its formal stages once. -/
private def positive {clearance : Certificate source} (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "the mixed family fixture became constant")
  | .positive _ _, locations => check locations (Stages.prepareInput _)

/-- Construct one original mixed inventory and its complete same-family paid formal association. -/
public def run : IO Unit := do
  let attempt := Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the mixed family fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "the mixed family fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive (Inventory.prepare margin.toCertificate (by decide +kernel))

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Family
