module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid finite observations of the original recurrence ledger

The same original ledger supplies fixed scalar weights, gains and physical
bounds before each request. Its retained selected-mode schedule determines
one backward whole-context budget. The actual common association then pays
that budget and reads the original formal modes and source equations.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence

open Purelib
open Purelib.LinearAlgebra.Matrix
open Purelib.Data.Vector
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Polynomial.Recurrence.Reading (values)

open Multiplicity.Roots.Stages.Reading renaming Request → StageRequest

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family}

variable {argument : PositiveArgument inventory} {rows : Nat}

namespace Request

/-- The original selected-mode schedule at this same ledger's fixed final scalar weight and gain. -/
abbrev Modes (retained : Recurrence argument rows) (epsilon : Rational) (count : Nat) :=
  Reading.Modes retained.bounds retained.boundary retained.parameters.finalWeight
    retained.parameters.finalGain epsilon count

end Request

set_option genInjectivity false in
/-- A sufficient common endpoint request computed before observing the original recurrence models.

The original selected generalized modes determine their sufficient finite
thresholds and a common endpoint tolerance. The original whole-context budget
then pays that exact tolerance using the ledger's already fixed parameters.
-/
structure Request (retained : Recurrence argument rows) (epsilon : Rational) (count : Nat) where
  /-- The requested finite quadrance bound is positive. -/
  epsilonPositive : 0 < epsilon
  /-- The original selected-mode schedules on the same fixed parameters and actual boundary orders. -/
  modes : Request.Modes retained epsilon count
  /-- The complete mode schedule is the original pre-observation construction on these exact parents. -/
  modes_eq : modes = Reading.Modes.prepare retained.bounds retained.boundary
    retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
    epsilon epsilonPositive count
  /-- The original backward whole-context request pays that same mode tolerance. -/
  stages : StageRequest retained.parameters modes.tolerance
  /-- Every original factor request is computed from the exact retained mode tolerance. -/
  stages_eq : stages = StageRequest.prepare retained.parameters modes.tolerance modes.tolerance_positive

constructive_injectivity Request

namespace Request

/-- Retain checked original mode schedules and the exact whole-context request without replaying either producer. -/
@[expose] def ofCaches (retained : Recurrence argument rows) (epsilon : Rational) (count : Nat)
    (epsilonPositive : 0 < epsilon) (modes : Modes retained epsilon count)
    (modesEq : modes = Reading.Modes.prepare retained.bounds retained.boundary
      retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
      epsilon epsilonPositive count)
    (stages : StageRequest retained.parameters modes.tolerance)
    (stagesEq : stages = StageRequest.prepare retained.parameters modes.tolerance modes.tolerance_positive) :
    Request retained epsilon count :=
  { epsilonPositive, modes, modes_eq := modesEq, stages, stages_eq := stagesEq }

/-- Prepare the same selected-mode thresholds and original backward budgets before constructing any model. -/
@[expose] def prepare (retained : Recurrence argument rows) (epsilon : Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) : Request retained epsilon count :=
  let modes := Reading.Modes.prepare retained.bounds retained.boundary retained.parameters.finalWeight
    retained.parameters.finalGain retained.parameters.finalGain_nonnegative epsilon epsilonPositive count
  let stages := StageRequest.prepare retained.parameters modes.tolerance modes.tolerance_positive
  ofCaches retained epsilon count epsilonPositive modes rfl stages rfl

variable {retained : Recurrence argument rows} {epsilon : Rational} {count : Nat}

/-- Checked original schedules and budgets restore the complete same pre-observation request. -/
theorem ofCaches_eq_prepare (retained : Recurrence argument rows) (epsilon : Rational) (count : Nat)
    (epsilonPositive : 0 < epsilon) (modes : Modes retained epsilon count)
    (modesEq : modes = Reading.Modes.prepare retained.bounds retained.boundary
      retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
      epsilon epsilonPositive count)
    (stages : StageRequest retained.parameters modes.tolerance)
    (stagesEq : stages = StageRequest.prepare retained.parameters modes.tolerance modes.tolerance_positive) :
    ofCaches retained epsilon count epsilonPositive modes modesEq stages stagesEq =
      prepare retained epsilon epsilonPositive count := by
  cases modesEq
  cases stagesEq
  rfl

/-- Every retained request restores its same original finite thresholds and backward budgets. -/
theorem restore (request : Request retained epsilon count) :
    request = prepare retained epsilon request.epsilonPositive count := by
  cases request with
  | mk positive modes modesEq stages stagesEq =>
      exact ofCaches_eq_prepare retained epsilon count positive modes modesEq stages stagesEq

/-- The exact original family association type paid by this same retained context budget. -/
abbrev Association (request : Request retained epsilon count) :=
  Reading.Bank.Association retained.prepared.separation.prepared.contexts_eq argument
    retained.bounds request.stages.budget

end Request

set_option genInjectivity false in
/-- The actual common model paying the same original finite-mode request.

The original family association retains every Exact or Higher factor cache
and the original stage realization. It consumes the already prepared request
and ledger without rebuilding any original bank, geometry or mode schedule.
-/
structure Observation {retained : Recurrence argument rows} {epsilon : Rational} {count : Nat}
    (request : Request retained epsilon count) where
  /-- The actual original common-root association at the retained backward budget. -/
  association : request.Association
  /-- The complete association is the original automatic procedure on these same caches. -/
  association_eq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages

constructive_injectivity Observation

namespace Observation

variable {retained : Recurrence argument rows} {epsilon : Rational} {count : Nat}
variable {request : Request retained epsilon count}

/-- Retain a checked actual common association without replaying any of its original factor models. -/
@[expose] def ofAssociation (request : Request retained epsilon count) (association : request.Association)
    (associationEq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages) :
    Observation request := { association, association_eq := associationEq }

/-- Construct the automatic original common association using the same fixed ledger and already prepared request. -/
@[expose] def prepare (request : Request retained epsilon count) : Observation request :=
  let association := Reading.Bank.prepare retained.prepared argument retained.bounds request.stages
  ofAssociation request association rfl

/-- Read the same actual final Gaussian reading directly from its retained original stage realization. -/
@[expose] def reading (observation : Observation request) := observation.association.model.finalReading

/-- The actual reading has exactly the gain fixed before the original mode schedules and observations. -/
theorem gain_eq (observation : Observation request) :
    observation.reading.gain = retained.parameters.finalGain := observation.association.final_gain

/-- The actual original common endpoint pays the exact selected-mode tolerance. -/
theorem error_lt (observation : Observation request) : observation.reading.error < request.modes.tolerance :=
  observation.association.error_lt

/-- The same actual original endpoint weakly pays every retained selected-mode request. -/
theorem error_le (observation : Observation request) : observation.reading.error ≤ request.modes.tolerance :=
  observation.association.error_le

/-- Every original embedded Gaussian coefficient is read exactly by the same actual common model. -/
theorem read_scalar (observation : Observation request) (value : Canonical) :
    observation.reading.read (retained.prepared.separation.prepared.stages.embed value) = value :=
  observation.association.read_scalar value

/-- Every requested finite selected mode is small at its actual original formal root and generalized order.

The quantitative root bound is proved from the same original owner and
retained factor association. The original finite schedule then pays its
actual formal mode; observed-root powers are not substituted for that mode.
-/
theorem window_lt (observation : Observation request) (column : Fin retained.owners.selection.word.length)
    (offset : Fin count) :
    Norm.Basic.normSq (observation.reading.read
      (Polynomial.Recurrence.Mode.window
        (retained.prepared.bank.block
          (Polynomial.Recurrence.Mode.Reading.Selected.original retained.owners.selection column)).point
        (request.modes.orders.orders column)
        ((request.modes.schedule.entryAt column).inside.index + count)
        ((request.modes.schedule.entryAt column).index offset))) < epsilon :=
  request.modes.window_lt observation.reading observation.gain_eq observation.error_le column
    (Reading.Bank.inside retained.prepared retained.owners observation.association _
      (retained.owners.accepted column)) offset

/-- The actual original truncated recurrence row reads through its same Gaussian source and finite input window. -/
theorem row_eq (observation : Observation request) {length : Nat}
    (input : Vec retained.prepared.separation.Scalar length) (index : Nat) :
    observation.reading.read (Polynomial.Recurrence.row retained.prepared.mapped rows input index) =
      Polynomial.Recurrence.row source rows
        (values observation.reading input) index := by
  rewrite [retained.prepared.mapped_eq]
  exact Polynomial.Recurrence.Reading.row_eq observation.reading
    (Multiplicity.Roots.Stages.Images.coefficientMap_zero _ rfl) source rows input index

/-- The same actual complete startup vector reads exactly through the original Gaussian source coefficients. -/
theorem boundary_eq (observation : Observation request) {length : Nat}
    (input : Vec retained.prepared.separation.Scalar length) :
    values observation.reading
        (Polynomial.Recurrence.boundary retained.prepared.mapped rows input) =
      Polynomial.Recurrence.boundary source rows
        (values observation.reading input) := by
  rewrite [retained.prepared.mapped_eq]
  exact Polynomial.Recurrence.Reading.boundary_eq observation.reading
    (Multiplicity.Roots.Stages.Images.coefficientMap_zero _ rfl) source rows input

/-- The same actual selected formal columns satisfy every original Gaussian source recurrence row after reading. -/
theorem selected_equations (observation : Observation request) :
    Polynomial.Recurrence.Boundary.Equations source rows
      (Vec.map (values observation.reading)
        retained.boundary.selected.result.readings.values) := by
  have original := Polynomial.Recurrence.Boundary.Hermite.equations retained.prepared.bank
    (Boundary.mapped_normalized retained.prepared) retained.boundary.selected.result.readings
    (Nat.le_refl _) retained.boundary.selected.selection.admissible
  have mapped := Eq.mp (congrArg
    (fun polynomial : Polynomial.Dense.Basic.DensePolynomial retained.prepared.separation.Scalar =>
      Polynomial.Recurrence.Boundary.Equations polynomial rows retained.boundary.selected.result.readings.values)
    retained.prepared.mapped_eq) original
  exact Polynomial.Recurrence.Reading.equations observation.reading
    (Multiplicity.Roots.Stages.Images.coefficientMap_zero _ rfl) source rows _ mapped

/-- A retained checked original association restores the complete automatic observation. -/
theorem ofAssociation_eq_prepare (request : Request retained epsilon count) (association : request.Association)
    (associationEq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages) :
    ofAssociation request association associationEq = prepare request := by
  cases associationEq
  rfl

/-- The same actual common model restores its original automatic observation without reconstructing parents. -/
theorem restore (observation : Observation request) : observation = prepare request := by
  cases observation with
  | mk association associationEq => exact ofAssociation_eq_prepare request association associationEq

end Observation

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence

end
