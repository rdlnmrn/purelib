module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Modes
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Parameters
import Purelib.Polynomial.Winding.Circle.Operations

/-!
# Mode caches from actual original zero and repeated-root inventories

Each original whole-circle source supplies its automatic inventory, formal
bank, retained owners and actual boundary. The same prepared argument bounds
choose the original stage parameters before observations. The mode adapter
then preserves the expected original generalized orders and physical ceilings.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Modes

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.Multiplicity.Circle
open Purelib.RootIsolation.Multiplicity.Circle.Roots
open Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

/-- The original double zero retains both transient generalized coordinates. -/
private def zeroSource : CoefficientPolynomial := ⟨[1, 0, 0]⟩

/-- The original repeated interior factor retains its actual normalized coefficient table. -/
private def repeatedSource : CoefficientPolynomial := ⟨[1, -1, 1 / 4]⟩

/-- The original zero-factor circle margin certifies the same double-zero source. -/
private def zeroClearance : Certificate zeroSource :=
  have same : Power.polynomialPower (LinearFactor.linearFactor 0) 2 = zeroSource := by decide +kernel
  same ▸ (Certificate.linearInside 0 (by decide +kernel)).power 2

/-- The same original interior linear margin certifies its actual repeated-root coefficient product. -/
private def repeatedClearance : Certificate repeatedSource :=
  have same : Power.polynomialPower (LinearFactor.linearFactor (⟨1 / 2, 0⟩ : Canonical)) 2 = repeatedSource :=
    by decide +kernel
  same ▸ (Certificate.linearInside (⟨1 / 2, 0⟩ : Canonical) (by decide +kernel)).power 2

/-- Both actual source coefficient tables are already normalized. -/
private theorem normalized : zeroSource.normalize = zeroSource ∧ repeatedSource.normalize = repeatedSource :=
  by decide +kernel

/-- Read expected original orders and physical ceilings through the complete automatic preparation chain.

The zero-row boundary needs no unit premise and retains the original actual
occurrence cache. The source-fixed stage radii read the same prepared bound
family after its original context equality, without another context owner.
-/
private def rows (source : CoefficientPolynomial) (clearance : Certificate source)
    (sourceNormalized : source.normalize = source) : List (Nat × Rational) :=
  let inventory := Inventory.prepare clearance sourceNormalized
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => []
  | .positive input _, locations =>
      let prepared := Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.prepare input
      let owners := Owners.prepare prepared locations
      let boundary := Roots.Boundary.prepare owners 0 (fun impossible => False.elim (Nat.not_lt_zero 0 impossible))
      let argument := PositiveArgument.prepare locations
      let bounds := Bounds.Family.prepare argument
      let contextsEq := congrArg List.length prepared.separation.prepared.contexts_eq
      let radii := fun index => bounds.radii (Fin.cast contextsEq index)
      let parameters := Stages.Reading.Parameters.prepare prepared.separation.prepared.stages Norm.weight 1
        radii (by decide) (fun index => bounds.radii_nonnegative (Fin.cast contextsEq index))
      let modes := Modes.prepare bounds boundary parameters.finalWeight parameters.finalGain
        parameters.finalGain_nonnegative 1 (by decide) 2
      List.ofFn (fun column : Fin owners.selection.word.length =>
        (modes.orders.orders column,
          modes.ceilings (Purelib.Polynomial.Recurrence.Mode.Reading.Selected.original owners.selection column)))

/-- The complete original double-zero chain preserves both orders and its exact zero ceiling. -/
private theorem original_zero_rows : rows zeroSource zeroClearance normalized.left = [(0, 0), (1, 0)] :=
  by decide +kernel

/-- The complete original repeated-root chain preserves both orders and its independently computed quarter ceiling. -/
private theorem original_repeated_rows :
    rows repeatedSource repeatedClearance normalized.right = [(0, 1 / 4), (1, 1 / 4)] := by decide +kernel

/-- The same actual cache entries restore the original mode adapter without replaying its parent constructions. -/
private theorem restore {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input} {prepared : Prepared input}
    {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory}
    {owners : Owners prepared inventory} {rows : Nat} {bounds : Bounds.Family argument}
    {boundary : Roots.Boundary owners rows} {weight : Purelib.Algebra.Ring.Weight prepared.separation.Scalar}
    {gain epsilon : Rational} {count : Nat} (retained : Modes bounds boundary weight gain epsilon count) :
    Modes.ofCaches bounds boundary weight gain epsilon count retained.gainNonnegative retained.epsilonPositive
      retained.ceilings retained.ceilings_eq retained.ceilingsNonnegative retained.ceilingsInside
      retained.orders retained.orders_eq retained.schedule retained.schedule_eq = retained := rfl

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Modes
