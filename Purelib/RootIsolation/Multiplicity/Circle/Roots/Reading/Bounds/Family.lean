module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds
import Purelib.Data.List.DependentProduct
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stored physical bounds in original positive-context order

The same inventory and argument supply one retained bound entry at every
original context occurrence. Stage radii project those cached entries,
without observing roots or preparing another argument or bound family.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds

open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Clearance.Circle (Certificate)

variable {source opposite : CoefficientPolynomial} {clearance : Certificate source}
variable {input : PositiveSideInput source opposite} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family}

namespace Family

/-- The original bound-entry type at one same inventory and argument context occurrence. -/
abbrev Entry (argument : PositiveArgument inventory) (index : Fin input.contexts.length) :=
  Bounds (inventory.factorAt index).observation (inventory.factorAt index).locations (argument.argumentAt index)

end Family

set_option genInjectivity false in
/-- Stored bounds for every same original positive inventory context and argument.

The original dependent product retains each actual entry once. Its defining
equation identifies the original context-wise preparation without retaining
a function that recomputes the entries on lookup.
-/
structure Family (argument : PositiveArgument inventory) where
  /-- The actual bound entry at every original bounded context occurrence. -/
  entries : DependentProduct input.contexts (Family.Entry argument)
  /-- The entries are the original materialized bound constructors on those same retained parents. -/
  entries_eq : entries = DependentProduct.ofFn input.contexts (fun index =>
    Bounds.prepare (inventory.factorAt index).observation (inventory.factorAt index).locations
      (argument.argumentAt index))

constructive_injectivity Family

namespace Family

/-- Retain checked saved entries without rerunning any original bound or argument constructor. -/
@[expose] def ofEntries (argument : PositiveArgument inventory)
    (entries : DependentProduct input.contexts (Entry argument))
    (entriesEq : entries = DependentProduct.ofFn input.contexts (fun index =>
      Bounds.prepare (inventory.factorAt index).observation (inventory.factorAt index).locations
        (argument.argumentAt index))) : Family argument :=
  { entries, entries_eq := entriesEq }

/-- Materialize the original physical bound at each original context occurrence exactly once. -/
@[expose] def prepare (argument : PositiveArgument inventory) : Family argument :=
  let entries := DependentProduct.ofFn input.contexts (fun index =>
    Bounds.prepare (inventory.factorAt index).observation (inventory.factorAt index).locations
      (argument.argumentAt index))
  ofEntries argument entries rfl

variable {argument : PositiveArgument inventory}

/-- Read the same stored bound entry at its original bounded context position. -/
@[expose] def boundsAt (retained : Family argument) (index : Fin input.contexts.length) : Entry argument index :=
  DependentProduct.get input.contexts retained.entries index

/-- Stored bound lookup returns the complete original constructor on the same inventory and argument entries. -/
theorem boundsAt_eq (retained : Family argument) (index : Fin input.contexts.length) :
    retained.boundsAt index = Bounds.prepare (inventory.factorAt index).observation
      (inventory.factorAt index).locations (argument.argumentAt index) :=
  (congrArg (fun entries => DependentProduct.get input.contexts entries index) retained.entries_eq).trans
    (DependentProduct.get_ofFn _ _ index)

/-- The original context radius function reads only the same stored bound radii. -/
@[expose] def radii (retained : Family argument) (index : Fin input.contexts.length) : Rational :=
  (retained.boundsAt index).radius

/-- Every same original context radius is nonnegative before formal model observations. -/
theorem radii_nonnegative (retained : Family argument) (index : Fin input.contexts.length) :
    0 ≤ retained.radii index := (retained.boundsAt index).radius_nonnegative

/-- Checked saved entries restore the complete original family constructor. -/
theorem ofEntries_eq_prepare (argument : PositiveArgument inventory)
    (entries : DependentProduct input.contexts (Entry argument))
    (entriesEq : entries = DependentProduct.ofFn input.contexts (fun index =>
      Bounds.prepare (inventory.factorAt index).observation (inventory.factorAt index).locations
        (argument.argumentAt index))) : ofEntries argument entries entriesEq = prepare argument := by
  cases entriesEq
  rfl

/-- The complete retained bound family restores its same original preparation. -/
theorem restore (retained : Family argument) : retained = prepare argument := by
  cases retained with
  | mk entries entriesEq => exact ofEntries_eq_prepare argument entries entriesEq

end Family
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds

end
