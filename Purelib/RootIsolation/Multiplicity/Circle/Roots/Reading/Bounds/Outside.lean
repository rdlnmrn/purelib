module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Owners
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# One retained floor for the original outside root occurrences

The original owner labels select outside blocks before any reading is
observed. Their cached physical floors supply positive excesses above one.
One finite minimum retains a common floor, including the empty selection.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.List
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Prepared)
open Purelib.Polynomial.Clearance.Circle (Certificate)

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
variable {argument : PositiveArgument inventory}

set_option genInjectivity false in
/-- Cached outside labels, original physical floors and their common strict lower endpoint.

Only original outside labels use their floor minus one in the finite
minimum. Inside blocks use the harmless positive entry one. The minimum's
positive default also handles an empty outside selection, without imposing
an outside condition on any inside or zero root.
-/
structure Outside (bounds : Family argument) (owners : Owners prepared inventory) where
  /-- The outside labels are materialized once in original block order. -/
  selected : Vec Bool prepared.bank.blocks.length
  /-- Every outside label is the complement of the same retained inside label. -/
  selected_eq : selected = vectorOfFn (fun index => !owners.selection.labels index)
  /-- The original physical floor is retained once at each original owner. -/
  floors : Vec Rational prepared.bank.blocks.length
  /-- Each floor consumes the same original context's cached bound. -/
  floors_eq : floors = vectorOfFn (fun index => (bounds.boundsAt (owners.occurrences index).context).floor)
  /-- The finite positive excess table reuses those same label and floor caches. -/
  excesses : List Rational
  /-- Outside floors contribute their excess above one; other blocks contribute one. -/
  excesses_eq : excesses = List.ofFn (fun index => if selected index then floors index - 1 else 1)
  /-- The finite excess minimum is computed once. -/
  minimum : Rational
  /-- The retained minimum belongs to that exact displayed excess table. -/
  minimum_eq : minimum = Minimum.positiveMinimum excesses
  /-- The common physical floor is computed from the same retained minimum. -/
  commonFloor : Rational
  /-- Adding one transports the positive excess back to root quadrance. -/
  commonFloor_eq : commonFloor = 1 + minimum

constructive_injectivity Outside

namespace Outside

/-- Prepare one original outside-floor cache without observing roots or recomputing their bound family. -/
@[expose] def prepare (bounds : Family argument) (owners : Owners prepared inventory) : Outside bounds owners :=
  let selected := vectorOfFn (fun index => !owners.selection.labels index)
  let floors := vectorOfFn (fun index => (bounds.boundsAt (owners.occurrences index).context).floor)
  let excesses := List.ofFn (fun index => if selected index then floors index - 1 else 1)
  let minimum := Minimum.positiveMinimum excesses
  let commonFloor := 1 + minimum
  { selected, selected_eq := rfl, floors, floors_eq := rfl, excesses, excesses_eq := rfl
    minimum, minimum_eq := rfl, commonFloor, commonFloor_eq := rfl }

variable {bounds : Family argument} {owners : Owners prepared inventory}

/-- A retained outside label complements the same original geometric occurrence's inside decision. -/
theorem selected_at (retained : Outside bounds owners) (index : Fin prepared.bank.blocks.length) :
    retained.selected index = !(owners.occurrences index).inside inventory := by
  rewrite [retained.selected_eq, vectorOfFn_apply, owners.labels_eq]
  rfl

/-- A retained selected occurrence carries the actual original outside decision. -/
theorem outside (retained : Outside bounds owners) (index : Fin prepared.bank.blocks.length)
    (selected : retained.selected index = true) : (owners.occurrences index).inside inventory = false := by
  rewrite [retained.selected_at index] at selected
  cases original : (owners.occurrences index).inside inventory with
  | false => rfl
  | true => rewrite [original] at selected; cases selected

/-- Each retained floor reads only the same original owner and cached context bound. -/
theorem floors_at (retained : Outside bounds owners) (index : Fin prepared.bank.blocks.length) :
    retained.floors index = (bounds.boundsAt (owners.occurrences index).context).floor := by
  rewrite [retained.floors_eq, vectorOfFn_apply]
  rfl

/-- Every selected original floor is strictly greater than unit quadrance. -/
theorem floorAboveOne (retained : Outside bounds owners) (index : Fin prepared.bank.blocks.length)
    (selected : retained.selected index = true) : 1 < retained.floors index := by
  rewrite [retained.floors_at index]
  have original := retained.outside index selected
  change Locations.insideAt (inventory.factorAt (owners.occurrences index).context).observation
    (inventory.factorAt (owners.occurrences index).context).locations (owners.occurrences index).localRoot = false
    at original
  exact (bounds.boundsAt (owners.occurrences index).context).outside_floor
    (owners.occurrences index).localRoot original

/-- Every original excess entry is positive, including entries at inside blocks. -/
theorem excess_positive (retained : Outside bounds owners) (value : Rational)
    (member : value ∈ retained.excesses) : 0 < value := by
  rewrite [retained.excesses_eq] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  cases selected : retained.selected index with
  | false =>
      rewrite [selected] at equal
      exact equal ▸ (by decide : (0 : Rational) < 1)
  | true =>
      rewrite [selected] at equal
      exact equal ▸ Arithmetic.sub_pos_direct (retained.floorAboveOne index selected)

/-- The retained finite excess minimum is positive without an outside nonemptiness premise. -/
theorem minimum_positive (retained : Outside bounds owners) : 0 < retained.minimum := by
  rewrite [retained.minimum_eq]
  exact Minimum.positiveMinimum_pos retained.excesses retained.excess_positive

/-- The common cached endpoint lies strictly beyond the unit circle. -/
theorem commonFloorAboveOne (retained : Outside bounds owners) : 1 < retained.commonFloor := by
  rewrite [retained.commonFloor_eq]
  have positive := Arithmetic.add_lt_add_left_direct retained.minimum_positive 1
  rewrite [add_zero] at positive
  exact positive

/-- The same common endpoint is bounded by every actual selected original floor. -/
theorem common_le (retained : Outside bounds owners) (index : Fin prepared.bank.blocks.length)
    (selected : retained.selected index = true) : retained.commonFloor ≤ retained.floors index := by
  have member : retained.floors index - 1 ∈ retained.excesses := by
    rewrite [retained.excesses_eq]
    apply OfFn.Basic.mem_ofFn.mpr
    refine ⟨index, ?_⟩
    rewrite [selected]
    rfl
  have smaller := Minimum.positiveMinimum_le_of_mem member
  rewrite [← retained.minimum_eq] at smaller
  have shifted := Arithmetic.add_le_add_direct (le_refl (1 : Rational)) smaller
  rewrite [retained.commonFloor_eq]
  exact shifted.trans_eq (by ring1)

/-- Complete retained cache equations restore the original source-fixed constructor. -/
theorem restore (retained : Outside bounds owners) : retained = prepare bounds owners := by
  cases retained with
  | mk selected selectedEq floors floorsEq excesses excessesEq minimum minimumEq commonFloor commonFloorEq =>
      cases selectedEq
      cases floorsEq
      cases excessesEq
      cases minimumEq
      cases commonFloorEq
      rfl

end Outside
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds

end
