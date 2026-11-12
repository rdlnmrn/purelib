module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Selection
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Selected coordinates in the same original complete recurrence ledger

The retained selected boundary and complete characteristic basis have the
same full root word. A certified coordinate inclusion and a bound-only view
of that original basis connect their exact trajectories and startup kernels.
Neither roots nor the original basis are reconstructed.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence.Mode (Hermite)
open Purelib.LinearAlgebra.Matrix

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory} {rows : Nat}

namespace Selection

/-- The selected/full coordinate cache on this same retained original boundary selection. -/
abbrev CoordinateMap (ledger : Recurrence argument rows) :=
  Word.Selection.Coordinates ledger.boundary.selected.selection

/-- The original complete Hermite owner at the same boundary selection's full-word index. -/
abbrev Basis (ledger : Recurrence argument rows) :=
  Hermite ledger.prepared.bank.blocks ledger.prepared.bank.differenceInverses
    ledger.boundary.selected.selection.fullWord

/-- The complete recurrence and selected boundary retain the same full original multiplicity word. -/
theorem word_eq (ledger : Recurrence argument rows) :
    ledger.recurrence.fullWord = ledger.boundary.selected.selection.fullWord :=
  ledger.recurrence.fullWord_eq.trans ledger.boundary.selected.selection.fullWord_eq.symm

/-- A bound-only view of the same retained complete source basis, with no basis producer call. -/
@[expose] def originalBasis (ledger : Recurrence argument rows) : Basis ledger :=
  Eq.ndrec (motive := fun word => Hermite ledger.prepared.bank.blocks ledger.prepared.bank.differenceInverses word)
    ledger.recurrence.basis (word_eq ledger)

end Selection

set_option genInjectivity false in
/-- A cached selected/full coordinate inclusion tied to the same original complete recurrence basis.

The coordinate map consumes the retained boundary selection. Its complete
basis is only the original ledger basis with equal full-word bounds
transported; its matrix and inverse data remain the same retained values.
-/
structure Selection (ledger : Recurrence argument rows) where
  /-- The actual selected/full inclusion on the same retained selection. -/
  coordinates : Selection.CoordinateMap ledger
  /-- The map is the original constructor on that same cached selected word. -/
  coordinates_eq : coordinates = Word.Selection.Coordinates.prepare ledger.boundary.selected.selection
  /-- The same complete source basis at the boundary's full-word index. -/
  basis : Selection.Basis ledger
  /-- Only the original basis's equal full-word bounds have been transported. -/
  basis_eq : basis = Selection.originalBasis ledger

constructive_injectivity Selection

namespace Selection

/-- Retain certified coordinate and original-basis caches without invoking either producer. -/
@[expose] def ofCaches (ledger : Recurrence argument rows) (coordinates : CoordinateMap ledger)
    (coordinatesEq : coordinates = Word.Selection.Coordinates.prepare ledger.boundary.selected.selection)
    (basis : Basis ledger) (basisEq : basis = originalBasis ledger) : Selection ledger :=
  { coordinates, coordinates_eq := coordinatesEq, basis, basis_eq := basisEq }

/-- Cache the inclusion once and retain the same original full basis through its full-word identity. -/
@[expose] def prepare (ledger : Recurrence argument rows) : Selection ledger :=
  let coordinates := Word.Selection.Coordinates.prepare ledger.boundary.selected.selection
  let basis := originalBasis ledger
  ofCaches ledger coordinates rfl basis rfl

variable {ledger : Recurrence argument rows}

/-- The original startup observation horizon contains one complete source characteristic prefix. -/
theorem room (_retained : Selection ledger) :
    ledger.boundary.selected.selection.fullWord.length ≤ Boundary.horizon ledger.prepared rows := by
  have lengthEq := (congrArg List.length
    (ledger.boundary.selected.selection.fullWord_eq.trans ledger.recurrence.fullWord_eq.symm)).trans
      ledger.recurrence.source_count
  rewrite [lengthEq, Boundary.horizon_eq_source]
  change source.normalize.coeffs.length - 1 ≤ rows + source.coeffs.length
  rewrite [input.sourceNormalized]
  exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_left _ _)

/-- Every finite horizon of the same transported original basis satisfies the original source recurrence. -/
theorem horizon_satisfies (retained : Selection ledger) (count : Nat)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.fullWord.length) :
    ledger.recurrence.companion.Satisfies (Rectangular.apply (retained.basis.horizon count) coefficients) := by
  rewrite [retained.basis_eq]
  have transported (word : List (Fin ledger.prepared.bank.blocks.length))
      (same : ledger.recurrence.fullWord = word) (values : Vec ledger.prepared.separation.Scalar word.length) :
      ledger.recurrence.companion.Satisfies (Rectangular.apply
        ((Eq.ndrec
          (motive := fun word => Hermite ledger.prepared.bank.blocks ledger.prepared.bank.differenceInverses word)
          ledger.recurrence.basis same).horizon count) values) := by
    cases same
    exact ledger.recurrence.horizon_satisfies count values
  exact transported _ (word_eq ledger) coefficients

/-- The same full-source horizon acts exactly as the original selected trajectory on included coordinates. -/
theorem horizon_extend (retained : Selection ledger)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.word.length) :
    Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows))
        (retained.coordinates.extend coefficients) =
      Rectangular.apply (Rectangular.transpose ledger.boundary.selected.result.readings.values) coefficients :=
  Hermite.horizon_extend retained.coordinates retained.basis ledger.boundary.selected.result.readings coefficients

/-- The same complete original inverse recovers exactly the selected coefficients' zero extension. -/
theorem selected_coordinates (retained : Selection ledger)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.word.length) :
    retained.basis.coordinates (Split.take retained.room
      (Rectangular.apply (Rectangular.transpose ledger.boundary.selected.result.readings.values) coefficients)) =
        retained.coordinates.extend coefficients :=
  Hermite.selected_coordinates retained.coordinates retained.basis ledger.boundary.selected.result.readings
    retained.room coefficients

/-- Exact rejected-coordinate support identifies the same original selected trajectory.

The premise is equality to zero in the original coefficient ring. Physical
vanishing under a particular reading does not supply this formal support.
-/
theorem horizon_restrict (retained : Selection ledger)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.fullWord.length)
    (supported : ∀ index : Fin ledger.boundary.selected.selection.fullWord.length,
      ledger.boundary.selected.selection.labels
        (ledger.boundary.selected.selection.fullWord[index.val]'index.isLt) = false → coefficients index = 0) :
    Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows)) coefficients =
      Rectangular.apply (Rectangular.transpose ledger.boundary.selected.result.readings.values)
        (retained.coordinates.restrict coefficients) :=
  Hermite.horizon_restrict retained.coordinates retained.basis ledger.boundary.selected.result.readings
    coefficients supported

/-- Original startup rows of an included selected vector equal its same retained boundary matrix action. -/
theorem startup_extend (retained : Selection ledger)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.word.length) :
    Purelib.Polynomial.Recurrence.boundary ledger.prepared.mapped rows
      (Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows))
        (retained.coordinates.extend coefficients)) =
          Rectangular.apply ledger.boundary.selected.result.boundary coefficients :=
  Hermite.startup_extend retained.coordinates retained.basis ledger.boundary.selected.result coefficients

/-- Same-ledger free coordinates give zero left startup and every complete finite source-recurrence row. -/
theorem kernel_extend (retained : Selection ledger)
    (free : Vec ledger.prepared.separation.Scalar
      (ledger.boundary.selected.selection.word.length - ledger.boundary.selected.result.normal.rank)) :
    Purelib.Polynomial.Recurrence.boundary ledger.prepared.mapped rows
        (Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows))
          (retained.coordinates.extend (ledger.boundary.selected.result.normal.kernelVector free))) =
            vectorOfFn (fun _ => 0) ∧
      ledger.recurrence.companion.Satisfies
        (Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows))
          (retained.coordinates.extend (ledger.boundary.selected.result.normal.kernelVector free))) :=
  Hermite.kernel_extend retained.coordinates retained.basis ledger.boundary.selected.result
    ledger.recurrence.companion free

/-- Zero original startup rows characterize the same selected free kernel coordinates in the full basis. -/
theorem kernel_extend_iff (retained : Selection ledger)
    (coefficients : Vec ledger.prepared.separation.Scalar ledger.boundary.selected.selection.word.length) :
    Purelib.Polynomial.Recurrence.boundary ledger.prepared.mapped rows
        (Rectangular.apply (retained.basis.horizon (Boundary.horizon ledger.prepared rows))
          (retained.coordinates.extend coefficients)) = vectorOfFn (fun _ => 0) ↔
      ledger.boundary.selected.result.normal.kernelVector
        (ledger.boundary.selected.result.normal.kernelCoordinates coefficients) = coefficients :=
  Hermite.kernel_extend_iff retained.coordinates retained.basis ledger.boundary.selected.result coefficients

/-- Complete same-ledger cache equations restore this original coordinate bridge. -/
theorem restore (retained : Selection ledger) : retained = prepare ledger := by
  cases retained with
  | mk coordinates coordinatesEq basis basisEq =>
      cases coordinatesEq
      cases basisEq
      rfl

end Selection
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence

end
