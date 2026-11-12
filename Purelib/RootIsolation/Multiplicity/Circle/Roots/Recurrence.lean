module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Modes
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Recurrence
public import Purelib.Polynomial.Recurrence.Reading
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid recurrence coordinates at original geometric root owners

One original positive inventory supplies the actual formal bank, aligned
owners, physical bounds, complete source recurrence basis and selected startup
boundary. Fixed stage parameters precede every finite decay request. The
requested common reading preserves the original scalar recurrence rows while
paying the same selected generalized-mode schedules.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots

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

open Multiplicity.Roots.Stages.Reading renaming Request → StageRequest

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family}

set_option genInjectivity false in
/-- The actual original recurrence and startup normal form with fixed geometric model parameters.

The complete source companion and full Hermite basis remain distinct from
the selected boundary basis. All parents and expensive producers are retained
once with complete defining equations before any finite observation request.
-/
structure Recurrence (argument : PositiveArgument inventory) (rows : Nat) where
  /-- The original automatic formal roots, factor towers and final scalar algebra. -/
  prepared : Multiplicity.Roots.Prepared input
  /-- The formal roots use the same original positive input exactly. -/
  prepared_eq : prepared = Multiplicity.Roots.prepare input
  /-- The original geometric occurrences and their retained selected word. -/
  owners : Owners prepared inventory
  /-- The owner vector is the original alignment of the same formal and geometric parents. -/
  owners_eq : owners = Owners.prepare prepared inventory
  /-- The original per-factor physical radii and radial ceilings. -/
  bounds : Reading.Bounds.Family argument
  /-- The physical caches are the original once-materialized argument bounds. -/
  bounds_eq : bounds = Reading.Bounds.Family.prepare argument
  /-- The same full source companion and genuine complete Hermite basis. -/
  recurrence : Multiplicity.Roots.Recurrence prepared
  /-- The complete source recurrence is the original full-bank preparation. -/
  recurrence_eq : recurrence = Multiplicity.Roots.Recurrence.prepare prepared
  /-- The actual selected startup boundary, including its computed normal form. -/
  boundary : Boundary owners rows
  /-- The actual boundary consumes that same retained owner selection. -/
  boundary_eq : boundary = Boundary.prepare owners rows boundary.constantNonzero
  /-- The fixed original stage parameters at the same physical radii. -/
  parameters : Reading.Bank.Parameters prepared bounds
  /-- The parameter cache precedes observations and belongs to the same original stages. -/
  parameters_eq : parameters = Reading.Bank.prepareParameters prepared bounds

constructive_injectivity Recurrence

namespace Recurrence

/-- Retain the same checked original roots, owners, geometry, recurrence, boundary and fixed parameters. -/
@[expose] def ofCaches (argument : PositiveArgument inventory) (rows : Nat)
    (prepared : Multiplicity.Roots.Prepared input) (preparedEq : prepared = Multiplicity.Roots.prepare input)
    (owners : Owners prepared inventory) (ownersEq : owners = Owners.prepare prepared inventory)
    (bounds : Reading.Bounds.Family argument) (boundsEq : bounds = Reading.Bounds.Family.prepare argument)
    (recurrence : Multiplicity.Roots.Recurrence prepared)
    (recurrenceEq : recurrence = Multiplicity.Roots.Recurrence.prepare prepared)
    (boundary : Boundary owners rows)
    (boundaryEq : boundary = Boundary.prepare owners rows boundary.constantNonzero)
    (parameters : Reading.Bank.Parameters prepared bounds)
    (parametersEq : parameters = Reading.Bank.prepareParameters prepared bounds) : Recurrence argument rows :=
  { prepared, prepared_eq := preparedEq, owners, owners_eq := ownersEq, bounds, bounds_eq := boundsEq
    recurrence, recurrence_eq := recurrenceEq, boundary, boundary_eq := boundaryEq
    parameters, parameters_eq := parametersEq }

/-- Construct one original positive recurrence ledger before requesting a model observation.

Only positive startup rows require a nonzero original constant. True zero
roots therefore remain available at zero rows. The actual full source basis,
selected normal form and fixed stage parameters are each prepared once.
-/
@[expose] def prepare (argument : PositiveArgument inventory) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : Recurrence argument rows :=
  let prepared := Multiplicity.Roots.prepare input
  let owners := Owners.prepare prepared inventory
  let bounds := Reading.Bounds.Family.prepare argument
  let recurrence := Multiplicity.Roots.Recurrence.ofWord prepared
    owners.selection.fullWord owners.selection.fullWord_eq
  let boundary := Boundary.prepare owners rows nonzero
  let parameters := Reading.Bank.prepareParameters prepared bounds
  ofCaches argument rows prepared rfl owners rfl bounds rfl recurrence
    (Multiplicity.Roots.Recurrence.ofWord_eq_prepare prepared owners.selection.fullWord owners.selection.fullWord_eq)
    boundary rfl parameters rfl

variable {argument : PositiveArgument inventory} {rows : Nat}

/-- Read the actual complementary-target minus kernel dimension of the constructed original normal form. -/
@[expose] def defect (retained : Recurrence argument rows) : Int := retained.boundary.selected.result.normal.defect

/-- The actual constructed defect equals requested startup rows minus the independently retained inside multiplicity. -/
theorem defect_eq (retained : Recurrence argument rows) :
    retained.defect = (rows : Int) - (inventory.insideCount : Int) := retained.boundary.defect_eq

/-- The actual constructed identity block has the smaller of requested rows and original inside multiplicity. -/
theorem rank_eq (retained : Recurrence argument rows) :
    retained.boundary.selected.result.normal.rank = Nat.min rows inventory.insideCount := retained.boundary.rank_eq

/-- The same original kernel coordinate count follows from the actual retained normal form. -/
theorem kernel_dimension (retained : Recurrence argument rows) :
    retained.boundary.selected.result.normal.kernelDimension =
      inventory.insideCount - Nat.min rows inventory.insideCount := retained.boundary.kernel_dimension

/-- The same original complementary target count follows from the actual retained normal form. -/
theorem complement_dimension (retained : Recurrence argument rows) :
    retained.boundary.selected.result.normal.cokernelDimension =
      rows - Nat.min rows inventory.insideCount := retained.boundary.complement_dimension

/-- Every finite solution of the original full source recurrence has coordinates in its retained complete basis. -/
theorem reconstruct (retained : Recurrence argument rows) {count : Nat}
    (values : Vec retained.prepared.separation.Scalar count) (enough : retained.recurrence.fullWord.length ≤ count)
    (equations : retained.recurrence.companion.Satisfies values) :
    Rectangular.apply (retained.recurrence.basis.horizon count)
      (retained.recurrence.basis.coordinates (Split.take enough values)) = values :=
  retained.recurrence.horizon_reconstruct values enough equations

/-- The original full source inverse reconstructs every finite recurrence horizon, including shorter prefixes. -/
theorem reconstruct_any (retained : Recurrence argument rows) {count : Nat}
    (values : Vec retained.prepared.separation.Scalar count)
    (equations : retained.recurrence.companion.Satisfies values) :
    Rectangular.apply (retained.recurrence.basis.horizon count)
      (retained.recurrence.basis.coordinatesOfHorizon values) = values :=
  retained.recurrence.horizon_reconstruct_any values equations

/-- Checked original caches restore the complete positive recurrence preparation. -/
theorem ofCaches_eq_prepare (argument : PositiveArgument inventory) (rows : Nat)
    (prepared : Multiplicity.Roots.Prepared input) (preparedEq : prepared = Multiplicity.Roots.prepare input)
    (owners : Owners prepared inventory) (ownersEq : owners = Owners.prepare prepared inventory)
    (bounds : Reading.Bounds.Family argument) (boundsEq : bounds = Reading.Bounds.Family.prepare argument)
    (recurrence : Multiplicity.Roots.Recurrence prepared)
    (recurrenceEq : recurrence = Multiplicity.Roots.Recurrence.prepare prepared)
    (boundary : Boundary owners rows)
    (boundaryEq : boundary = Boundary.prepare owners rows boundary.constantNonzero)
    (parameters : Reading.Bank.Parameters prepared bounds)
    (parametersEq : parameters = Reading.Bank.prepareParameters prepared bounds) :
    ofCaches argument rows prepared preparedEq owners ownersEq bounds boundsEq recurrence recurrenceEq
      boundary boundaryEq parameters parametersEq = prepare argument rows boundary.constantNonzero := by
  cases preparedEq
  cases ownersEq
  cases boundsEq
  cases recurrenceEq
  cases parametersEq
  cases boundary with
  | mk nonzero constant constantEq selected selectedEq =>
      cases constantEq
      cases selectedEq
      rfl

/-- Retaining the complete ledger recovers its same original preparation at the original pole guard. -/
theorem restore (retained : Recurrence argument rows) :
    retained = prepare argument rows retained.boundary.constantNonzero := by
  cases retained with
  | mk prepared preparedEq owners ownersEq bounds boundsEq recurrence recurrenceEq
      boundary boundaryEq parameters parametersEq =>
      exact ofCaches_eq_prepare argument rows prepared preparedEq owners ownersEq bounds boundsEq
        recurrence recurrenceEq boundary boundaryEq parameters parametersEq

end Recurrence
end Purelib.RootIsolation.Multiplicity.Circle.Roots

end
