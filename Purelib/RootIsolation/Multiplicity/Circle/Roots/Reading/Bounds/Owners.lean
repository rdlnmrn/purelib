module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Owners
import Purelib.Data.Vector.Basic

/-!
# Original physical ceilings in retained formal-block order

The stored owner vector supplies each original context and local root. A
single finite vector reads its same already retained physical ceiling. The
original radial decision proves the selected ceilings strictly below one;
no assertion about an actual formal-root reading follows from its label.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Prepared)
open Purelib.Polynomial.Clearance.Circle (Certificate)

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
variable {argument : PositiveArgument inventory}

/-- Materialize original cached physical ceilings once in the same retained formal-block owner order. -/
@[expose] def ceilings (bounds : Family argument) (owners : Owners prepared inventory) :
    Vec Rational prepared.bank.blocks.length :=
  vectorOfFn (fun index => (bounds.boundsAt (owners.occurrences index).context).ceiling)

/-- Each materialized formal-block ceiling reads its same stored original context bound. -/
theorem ceilings_at (bounds : Family argument) (owners : Owners prepared inventory)
    (index : Fin prepared.bank.blocks.length) :
    bounds.ceilings owners index = (bounds.boundsAt (owners.occurrences index).context).ceiling :=
  vectorOfFn_apply _ index

/-- Every retained formal-block ceiling is nonnegative independently of its original radial label. -/
theorem ceilings_nonnegative (bounds : Family argument) (owners : Owners prepared inventory)
    (index : Fin prepared.bank.blocks.length) : 0 ≤ bounds.ceilings owners index := by
  rewrite [bounds.ceilings_at owners index]
  exact (bounds.boundsAt (owners.occurrences index).context).ceiling_nonnegative

/-- A selected original radial occurrence has a strictly interior cached physical ceiling.

The same retained context and local-root index select the original radial
decision. Its proved inside branch supplies the bound; no formal-root
realization or reading is selected by this statement.
-/
theorem ceilings_inside (bounds : Family argument) (owners : Owners prepared inventory)
    (index : Fin prepared.bank.blocks.length) (selected : owners.selection.labels index = true) :
    bounds.ceilings owners index < 1 := by
  rewrite [bounds.ceilings_at owners index]
  have inside := (owners.labels_eq index).symm.trans selected
  change Locations.insideAt (inventory.factorAt (owners.occurrences index).context).observation
    (inventory.factorAt (owners.occurrences index).context).locations (owners.occurrences index).localRoot = true
    at inside
  exact (bounds.boundsAt (owners.occurrences index).context).inside_ceiling
    (owners.occurrences index).localRoot inside

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family

end
