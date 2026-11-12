module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
public import Purelib.Polynomial.Recurrence.Mode.Reading.Combination
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid synchronized combinations in the original recurrence ledger

The same retained ledger supplies its original selected roots, boundary orders,
physical ceilings, coefficient algebra and fixed stage parameters. An actual
coefficient vector determines one synchronized finite-window request before
observations. Its one whole-context budget then constructs the same original
common reading, including all its geometric root bounds and paid errors.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination

open Purelib
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Multiplicity.Roots.Stages.Reading renaming Request → StageRequest, Budget → StageBudget

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory} {rows : Nat}

/-- The coefficient vector belongs to the same original selected word in its final scalar algebra. -/
abbrev Coefficients (retained : Recurrence argument rows) :=
  Vec retained.prepared.separation.Scalar retained.owners.selection.word.length

/-- The original boundary's occurrence cache is transported without reconstructing any mode orders. -/
abbrev Orders (retained : Recurrence argument rows) := Reading.Modes.Orders retained.owners

/-- The physical ceiling vector keeps the same original formal-block coordinates. -/
abbrev Ceilings (retained : Recurrence argument rows) := Vec Rational retained.prepared.bank.blocks.length

/-- The exact original synchronized schedule type keeps every source and coefficient owner. -/
abbrev Schedule (retained : Recurrence argument rows) (orders : Orders retained) (ceilings : Ceilings retained)
    (coefficients : Coefficients retained) (epsilon : Rational) (count : Nat) :=
  Polynomial.Recurrence.Mode.Reading.Combination retained.owners.selection orders retained.parameters.finalWeight
    retained.parameters.finalGain ceilings coefficients epsilon count

set_option genInjectivity false in
/-- A source-fixed synchronized-combination request and its one original whole-context payment.

No observation or final decay inequality is supplied. The original ledger's
bound and order caches prepare the same coefficient-weighted schedule, and
its strictly positive tolerance determines the complete backward stage request.
-/
structure Request (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (epsilon : Rational) (count : Nat) where
  /-- The finite combination quadrance request is positive. -/
  epsilonPositive : 0 < epsilon
  /-- The once-materialized original per-block physical ceilings. -/
  ceilings : Ceilings retained
  /-- The ceiling vector reads the same already retained geometric bounds and root owners. -/
  ceilings_eq : ceilings = retained.bounds.ceilings retained.owners
  /-- The same selected ceilings are nonnegative. -/
  ceilingsNonnegative : ∀ index, retained.owners.selection.labels index = true → 0 ≤ ceilings index
  /-- The same selected ceilings lie strictly inside the unit boundary. -/
  ceilingsInside : ∀ index, retained.owners.selection.labels index = true → ceilings index < 1
  /-- The same actual boundary's already retained generalized occurrence orders. -/
  orders : Orders retained
  /-- The order cache is just the original complete selection-equality transport. -/
  orders_eq : orders = Reading.Modes.boundaryOrders retained.boundary
  /-- The original synchronized coefficient-weighted schedule, prepared before observing a model. -/
  schedule : Schedule retained orders ceilings coefficients epsilon count
  /-- The complete schedule consumes those exact retained original caches. -/
  schedule_eq : schedule = Polynomial.Recurrence.Mode.Reading.Combination.prepare retained.owners.selection orders
    retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
    ceilings ceilingsNonnegative ceilingsInside coefficients epsilon epsilonPositive count
  /-- The original whole-context stage request pays that same computed endpoint tolerance. -/
  stages : StageRequest retained.parameters schedule.tolerance
  /-- The stage request is computed once from the same original schedule. -/
  stages_eq : stages = StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive

constructive_injectivity Request

namespace Request

/-- Retain checked complete schedules and budgets without replaying their producers or original parents. -/
@[expose] def ofCaches (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (epsilon : Rational) (count : Nat) (epsilonPositive : 0 < epsilon)
    (ceilings : Ceilings retained) (ceilingsEq : ceilings = retained.bounds.ceilings retained.owners)
    (ceilingsNonnegative : ∀ index, retained.owners.selection.labels index = true → 0 ≤ ceilings index)
    (ceilingsInside : ∀ index, retained.owners.selection.labels index = true → ceilings index < 1)
    (orders : Orders retained) (ordersEq : orders = Reading.Modes.boundaryOrders retained.boundary)
    (schedule : Schedule retained orders ceilings coefficients epsilon count)
    (scheduleEq : schedule = Polynomial.Recurrence.Mode.Reading.Combination.prepare retained.owners.selection orders
      retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
      ceilings ceilingsNonnegative ceilingsInside coefficients epsilon epsilonPositive count)
    (stages : StageRequest retained.parameters schedule.tolerance)
    (stagesEq : stages = StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive) :
    Request retained coefficients epsilon count :=
  { epsilonPositive, ceilings, ceilings_eq := ceilingsEq, ceilingsNonnegative, ceilingsInside
    orders, orders_eq := ordersEq, schedule, schedule_eq := scheduleEq, stages, stages_eq := stagesEq }

/-- Prepare one common weighted window and its original backward context budget before any observations. -/
@[expose] def prepare (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) (count : Nat) :
    Request retained coefficients epsilon count :=
  let ceilings := retained.bounds.ceilings retained.owners
  let ceilingsNonnegative := fun index (_ : retained.owners.selection.labels index = true) =>
    retained.bounds.ceilings_nonnegative retained.owners index
  let ceilingsInside := fun index accepted => retained.bounds.ceilings_inside retained.owners index accepted
  let orders := Reading.Modes.boundaryOrders retained.boundary
  let schedule := Polynomial.Recurrence.Mode.Reading.Combination.prepare retained.owners.selection orders
    retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
    ceilings ceilingsNonnegative ceilingsInside coefficients epsilon epsilonPositive count
  let stages := StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive
  ofCaches retained coefficients epsilon count epsilonPositive ceilings rfl ceilingsNonnegative ceilingsInside
    orders rfl schedule rfl stages rfl

variable {retained : Recurrence argument rows} {coefficients : Coefficients retained}
variable {epsilon : Rational} {count : Nat}

/-- The same request's displayed ceiling reads its original retained geometric context. -/
theorem ceilings_at (request : Request retained coefficients epsilon count)
    (index : Fin retained.prepared.bank.blocks.length) :
    request.ceilings index = (retained.bounds.boundsAt (retained.owners.occurrences index).context).ceiling :=
  (congrArg (fun values => values index) request.ceilings_eq).trans (retained.bounds.ceilings_at retained.owners index)

/-- Read the same original association type without rebuilding any stage or geometric owner. -/
abbrev Association (request : Request retained coefficients epsilon count) :=
  Reading.Bank.Association retained.prepared.separation.prepared.contexts_eq argument retained.bounds
    request.stages.budget

/-- Any same-ledger association paying the retained tolerance reads the synchronized original formal sum as small.

The association may come from a stronger common budget shared with another
request. Its actual same-root geometric bounds and fixed gain are reused;
equality to this specialized request's model producer is unnecessary.
-/
theorem association_window_lt (request : Request retained coefficients epsilon count)
    {target tolerance : Rational} {budget : StageBudget retained.parameters target tolerance}
    (association : Reading.Bank.Association retained.prepared.separation.prepared.contexts_eq argument
      retained.bounds budget) (paid : association.model.finalReading.error ≤ request.schedule.tolerance)
    (offset : Fin count) :
    Norm.Basic.normSq (association.model.finalReading.read (request.schedule.value offset)) < epsilon :=
  request.schedule.window_lt association.model.finalReading association.final_gain paid
    (fun column => (Reading.Bank.inside retained.prepared retained.owners association _
      (retained.owners.accepted column)).trans_eq (request.ceilings_at _).symm) offset

/-- The retained exact cache equations recover the complete same pre-observation request. -/
theorem ofCaches_eq_prepare (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (epsilon : Rational) (count : Nat) (epsilonPositive : 0 < epsilon)
    (ceilings : Ceilings retained) (ceilingsEq : ceilings = retained.bounds.ceilings retained.owners)
    (ceilingsNonnegative : ∀ index, retained.owners.selection.labels index = true → 0 ≤ ceilings index)
    (ceilingsInside : ∀ index, retained.owners.selection.labels index = true → ceilings index < 1)
    (orders : Orders retained) (ordersEq : orders = Reading.Modes.boundaryOrders retained.boundary)
    (schedule : Schedule retained orders ceilings coefficients epsilon count)
    (scheduleEq : schedule = Polynomial.Recurrence.Mode.Reading.Combination.prepare retained.owners.selection orders
      retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
      ceilings ceilingsNonnegative ceilingsInside coefficients epsilon epsilonPositive count)
    (stages : StageRequest retained.parameters schedule.tolerance)
    (stagesEq : stages = StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive) :
    ofCaches retained coefficients epsilon count epsilonPositive ceilings ceilingsEq ceilingsNonnegative ceilingsInside
      orders ordersEq schedule scheduleEq stages stagesEq =
        prepare retained coefficients epsilon epsilonPositive count := by
  cases ceilingsEq
  cases ordersEq
  cases scheduleEq
  cases stagesEq
  rfl

/-- The complete retained weighted request restores its original producer without reconstructing the ledger. -/
theorem restore (request : Request retained coefficients epsilon count) :
    request = prepare retained coefficients epsilon request.epsilonPositive count := by
  cases request with
  | mk positive ceilings ceilingsEq nonnegative inside orders ordersEq schedule scheduleEq stages stagesEq =>
      exact ofCaches_eq_prepare retained coefficients epsilon count positive ceilings ceilingsEq nonnegative inside
        orders ordersEq schedule scheduleEq stages stagesEq

end Request

set_option genInjectivity false in
/-- The actual common model paying a retained original synchronized-combination request.

Its original family association owns every exact or higher-factor observation
and the complete stage realization. The same parents and pre-observation
budget are reused without another bank, inventory or order construction.
-/
structure Observation {retained : Recurrence argument rows} {coefficients : Coefficients retained}
    {epsilon : Rational} {count : Nat} (request : Request retained coefficients epsilon count) where
  /-- The actual original common association at the stored backward budget. -/
  association : request.Association
  /-- The complete association is the original automatic procedure on the same retained caches. -/
  association_eq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages

constructive_injectivity Observation

namespace Observation

variable {retained : Recurrence argument rows} {coefficients : Coefficients retained}
variable {epsilon : Rational} {count : Nat} {request : Request retained coefficients epsilon count}

/-- Retain a checked actual association without replaying its original observations or stage realization. -/
@[expose] def ofAssociation (request : Request retained coefficients epsilon count) (association : request.Association)
    (associationEq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages) :
    Observation request := { association, association_eq := associationEq }

/-- Construct the original common model from the same ledger and computed synchronized request. -/
@[expose] def prepare (request : Request retained coefficients epsilon count) : Observation request :=
  let association := Reading.Bank.prepare retained.prepared argument retained.bounds request.stages
  ofAssociation request association rfl

/-- Read the already retained original common Gaussian interpretation. -/
@[expose] def reading (observation : Observation request) := observation.association.model.finalReading

/-- The actual common reading retains the same fixed pre-observation gain. -/
theorem gain_eq (observation : Observation request) :
    observation.reading.gain = retained.parameters.finalGain := observation.association.final_gain

/-- The actual common model strictly pays the same retained weighted-combination tolerance. -/
theorem error_lt (observation : Observation request) : observation.reading.error < request.schedule.tolerance :=
  observation.association.error_lt

/-- The same common model weakly pays every actual cached weighted-product coefficient. -/
theorem error_le (observation : Observation request) : observation.reading.error ≤ request.schedule.tolerance :=
  observation.association.error_le

/-- The actual original formal combination is small throughout its one computed common finite window. -/
theorem window_lt (observation : Observation request) (offset : Fin count) :
    Norm.Basic.normSq (observation.reading.read (request.schedule.value offset)) < epsilon :=
  request.association_window_lt observation.association observation.error_le offset

/-- Checked original observations recover the complete same automatic shared model. -/
theorem ofAssociation_eq_prepare (request : Request retained coefficients epsilon count)
    (association : request.Association)
    (associationEq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages) :
    ofAssociation request association associationEq = prepare request := by
  cases associationEq
  rfl

/-- The same retained shared observation restores its original procedure without reconstructing parents. -/
theorem restore (observation : Observation request) : observation = prepare request := by
  cases observation with
  | mk association associationEq => exact ofAssociation_eq_prepare request association associationEq

end Observation
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination

end
