module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Owners
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Boundary
public import Purelib.Polynomial.Recurrence.Mode.Reading.Selected
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Pre-observation mode schedules from original geometric owners and boundaries

The original owner vector supplies physical ceilings, and the actual boundary
supplies its same retained occurrence orders. Their exact cached transports
prepare the selected-mode schedule before observing any common model. Its
decay theorem still requires the actual same-root reading ceiling.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Prepared)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.Multiplicity.Circle

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
variable {argument : PositiveArgument inventory} {owners : Owners prepared inventory} {rows : Nat}

namespace Modes

/-- The same original selected-word occurrence cache, including its original generalized orders. -/
abbrev Orders (owners : Owners prepared inventory) := Occurrences owners.selection.word

/-- Transport the actual boundary's retained occurrence cache along its complete original selection equality. -/
@[expose] def boundaryOrders (boundary : Roots.Boundary owners rows) : Orders owners :=
  show Occurrences owners.selection.word from
    (congrArg Word.Selection.word boundary.selection_eq) ▸ boundary.selected.result.readings.occurrences

end Modes

set_option genInjectivity false in
/-- Cached selected-mode preparation on the same original inventory, bank and actual boundary.

Physical ceilings read one retained original bound per formal block. The
original boundary occurrence cache is transported once, without recomputing
orders. The same fixed weight and gain then supply one original selected
schedule; actual-reading radial bounds remain a separate theorem premise.
-/
structure Modes (bounds : Bounds.Family argument) (boundary : Roots.Boundary owners rows)
    (weight : Weight prepared.separation.Scalar) (gain epsilon : Rational) (count : Nat) where
  /-- The same pre-observation fixed gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The finite decay request is positive. -/
  epsilonPositive : 0 < epsilon
  /-- The once-materialized original physical ceilings in the existing bank block order. -/
  ceilings : Vec Rational prepared.bank.blocks.length
  /-- The ceiling vector reads the same original bound family and retained owners. -/
  ceilings_eq : ceilings = bounds.ceilings owners
  /-- The selected original-block ceilings are nonnegative. -/
  ceilingsNonnegative : ∀ index, owners.selection.labels index = true → 0 ≤ ceilings index
  /-- The same selected original-block ceilings lie strictly inside unit quadrance. -/
  ceilingsInside : ∀ index, owners.selection.labels index = true → ceilings index < 1
  /-- The same actual boundary's cached occurrence orders at the original selected word. -/
  orders : Modes.Orders owners
  /-- The order cache is only the original selection-equality transport of the actual boundary cache. -/
  orders_eq : orders = Modes.boundaryOrders boundary
  /-- The once-prepared original selected-mode schedule on these same retained inputs. -/
  schedule : Mode.Reading.Selected owners.selection orders weight gain ceilings epsilon count
  /-- The complete schedule is the same original pre-observation constructor. -/
  schedule_eq : schedule = Mode.Reading.Selected.prepare owners.selection orders weight gain gainNonnegative
    ceilings ceilingsNonnegative ceilingsInside epsilon epsilonPositive count

constructive_injectivity Modes

namespace Modes

/-- Retain checked original ceiling, order and mode-schedule caches without rerunning their producers. -/
@[expose] def ofCaches (bounds : Bounds.Family argument) (boundary : Roots.Boundary owners rows)
    (weight : Weight prepared.separation.Scalar) (gain epsilon : Rational) (count : Nat)
    (gainNonnegative : 0 ≤ gain) (epsilonPositive : 0 < epsilon)
    (ceilings : Vec Rational prepared.bank.blocks.length) (ceilingsEq : ceilings = bounds.ceilings owners)
    (ceilingsNonnegative : ∀ index, owners.selection.labels index = true → 0 ≤ ceilings index)
    (ceilingsInside : ∀ index, owners.selection.labels index = true → ceilings index < 1)
    (orders : Orders owners) (ordersEq : orders = boundaryOrders boundary)
    (schedule : Mode.Reading.Selected owners.selection orders weight gain ceilings epsilon count)
    (scheduleEq : schedule = Mode.Reading.Selected.prepare owners.selection orders weight gain gainNonnegative
      ceilings ceilingsNonnegative ceilingsInside epsilon epsilonPositive count) :
    Modes bounds boundary weight gain epsilon count :=
  { gainNonnegative, epsilonPositive, ceilings, ceilings_eq := ceilingsEq, ceilingsNonnegative, ceilingsInside
    orders, orders_eq := ordersEq, schedule, schedule_eq := scheduleEq }

/-- Prepare one original bound vector, reuse the actual boundary orders, and prepare one selected-mode schedule. -/
@[expose] def prepare (bounds : Bounds.Family argument) (boundary : Roots.Boundary owners rows)
    (weight : Weight prepared.separation.Scalar) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) (count : Nat) :
    Modes bounds boundary weight gain epsilon count :=
  let ceilings := bounds.ceilings owners
  let ceilingsNonnegative := fun index (_ : owners.selection.labels index = true) =>
    bounds.ceilings_nonnegative owners index
  let ceilingsInside := fun index accepted => bounds.ceilings_inside owners index accepted
  let orders := boundaryOrders boundary
  let schedule := Mode.Reading.Selected.prepare owners.selection orders weight gain gainNonnegative
    ceilings ceilingsNonnegative ceilingsInside epsilon epsilonPositive count
  ofCaches bounds boundary weight gain epsilon count gainNonnegative epsilonPositive ceilings rfl
    ceilingsNonnegative ceilingsInside orders rfl schedule rfl

variable {bounds : Bounds.Family argument} {boundary : Roots.Boundary owners rows}
variable {weight : Weight prepared.separation.Scalar} {gain epsilon : Rational} {count : Nat}

/-- Every stored ceiling reads the same original physical context at its retained owner coordinate. -/
theorem ceilings_at (retained : Modes bounds boundary weight gain epsilon count)
    (index : Fin prepared.bank.blocks.length) :
    retained.ceilings index = (bounds.boundsAt (owners.occurrences index).context).ceiling :=
  (congrArg (fun values => values index) retained.ceilings_eq).trans (bounds.ceilings_at owners index)

/-- Read the common endpoint tolerance from the same already prepared original mode schedule. -/
@[expose] def tolerance (retained : Modes bounds boundary weight gain epsilon count) : Rational :=
  retained.schedule.tolerance

/-- The same original endpoint tolerance is positive before any actual model reading is observed. -/
theorem tolerance_positive (retained : Modes bounds boundary weight gain epsilon count) :
    0 < retained.tolerance := retained.schedule.tolerance_positive

/-- A paid actual reading and its same original physical ceiling bound each requested original finite mode value.

The reading premise concerns the original formal root at the selected block
and its actual retained geometric context. It is not inferred from a Boolean
label; the original selected schedule supplies only the finite decay bound.
-/
theorem window_lt (retained : Modes bounds boundary weight gain epsilon count)
    {scalar : Canonical → prepared.separation.Scalar} (reading : GaussianReading weight scalar)
    (gain_eq : reading.gain = gain) (paid : reading.error ≤ retained.tolerance)
    (column : Fin owners.selection.word.length)
    (pointBound : Norm.Basic.normSq (reading.read
      (prepared.bank.block (Mode.Reading.Selected.original owners.selection column)).point) ≤
        (bounds.boundsAt (owners.occurrences (Mode.Reading.Selected.original owners.selection column)).context).ceiling)
    (offset : Fin count) :
    Norm.Basic.normSq (reading.read
      (Mode.window (prepared.bank.block (Mode.Reading.Selected.original owners.selection column)).point
        (retained.orders.orders column) ((retained.schedule.entryAt column).inside.index + count)
        ((retained.schedule.entryAt column).index offset))) < epsilon :=
  retained.schedule.window_lt reading gain_eq paid column
    (pointBound.trans_eq (retained.ceilings_at _).symm) offset

/-- Checked original caches recover the complete same pre-observation mode preparation. -/
theorem ofCaches_eq_prepare (bounds : Bounds.Family argument) (boundary : Roots.Boundary owners rows)
    (weight : Weight prepared.separation.Scalar) (gain epsilon : Rational) (count : Nat)
    (gainNonnegative : 0 ≤ gain) (epsilonPositive : 0 < epsilon)
    (ceilings : Vec Rational prepared.bank.blocks.length) (ceilingsEq : ceilings = bounds.ceilings owners)
    (ceilingsNonnegative : ∀ index, owners.selection.labels index = true → 0 ≤ ceilings index)
    (ceilingsInside : ∀ index, owners.selection.labels index = true → ceilings index < 1)
    (orders : Orders owners) (ordersEq : orders = boundaryOrders boundary)
    (schedule : Mode.Reading.Selected owners.selection orders weight gain ceilings epsilon count)
    (scheduleEq : schedule = Mode.Reading.Selected.prepare owners.selection orders weight gain gainNonnegative
      ceilings ceilingsNonnegative ceilingsInside epsilon epsilonPositive count) :
    ofCaches bounds boundary weight gain epsilon count gainNonnegative epsilonPositive ceilings ceilingsEq
      ceilingsNonnegative ceilingsInside orders ordersEq schedule scheduleEq =
        prepare bounds boundary weight gain gainNonnegative epsilon epsilonPositive count := by
  cases ceilingsEq
  cases ordersEq
  cases scheduleEq
  rfl

/-- The complete retained mode cache restores its same original preparation without rebuilding parents. -/
theorem restore (retained : Modes bounds boundary weight gain epsilon count) :
    retained = prepare bounds boundary weight gain retained.gainNonnegative epsilon retained.epsilonPositive count := by
  cases retained with
  | mk gainNonnegative epsilonPositive ceilings ceilingsEq ceilingsNonnegative ceilingsInside
      orders ordersEq schedule scheduleEq =>
      exact ofCaches_eq_prepare bounds boundary weight gain epsilon count gainNonnegative epsilonPositive
        ceilings ceilingsEq ceilingsNonnegative ceilingsInside orders ordersEq schedule scheduleEq

end Modes
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end
