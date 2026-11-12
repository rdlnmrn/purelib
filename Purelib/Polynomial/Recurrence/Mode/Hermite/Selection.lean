module

public import Purelib.Polynomial.Dense.Roots.Word.Selection.Coordinates
public import Purelib.Polynomial.Recurrence.Boundary.Hermite.Selected
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Solution

/-!
# The original selected boundary inside the complete source basis

One certified coordinate inclusion preserves the original root tags and
occurrence orders. The same full Hermite horizon therefore acts exactly as
the retained selected rectangle. Startup and free-kernel laws refer to that
same original full source trajectory, without a physical injectivity claim.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}
variable {selection : Word.Selection bank} {rows count : Nat}

/-- Each selected original column is its same complete source-basis column at the retained inclusion position. -/
theorem selected_column (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (rectangle : Rectangle bank.blocks bank.differenceInverses selection.word rows count)
    (index : Fin count) (column : Fin selection.word.length) :
    basis.horizon count index (coordinates.positions column) = Rectangular.transpose rectangle.values index column := by
  rw [horizon_at, Rectangular.transpose_apply, rectangle.values_at,
    coordinates.occurrence_order basis.occurrences rectangle.occurrences column]
  exact congrArg (fun tag => entry (point bank.blocks tag) (rectangle.occurrences.orders column) index.val)
    (coordinates.tags column)

/-- The complete original source horizon on zero-extended coordinates is exactly the same selected finite trajectory. -/
theorem horizon_extend (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (rectangle : Rectangle bank.blocks bank.differenceInverses selection.word rows count)
    (coefficients : Vec K selection.word.length) :
    Rectangular.apply (basis.horizon count) (coordinates.extend coefficients) =
      Rectangular.apply (Rectangular.transpose rectangle.values) coefficients := by
  apply vector_ext
  intro index
  rw [Rectangular.apply_at, Rectangular.apply_at]
  exact (coordinates.sum_extend (basis.horizon count index) coefficients).trans
    (sumFin_congr fun column => congrArg (· * coefficients column)
      (selected_column coordinates basis rectangle index column))

/-- Original complete coordinates of a sufficiently long selected trajectory are its same zero extension. -/
theorem selected_coordinates (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (rectangle : Rectangle bank.blocks bank.differenceInverses selection.word rows count)
    (room : selection.fullWord.length ≤ count) (coefficients : Vec K selection.word.length) :
    basis.coordinates (Split.take room
      (Rectangular.apply (Rectangular.transpose rectangle.values) coefficients)) = coordinates.extend coefficients := by
  rw [← horizon_extend coordinates basis rectangle coefficients]
  have firstRows : Split.take room
      (Rectangular.apply (basis.horizon count) (coordinates.extend coefficients)) =
        Rectangular.apply basis.matrix (coordinates.extend coefficients) := by
    apply vector_ext
    intro index
    rw [Split.take_apply, Rectangular.apply_at, Rectangular.apply_at]
    exact sumFin_congr fun column => congrArg (· * coordinates.extend coefficients column)
      (horizon_initial_row basis count _ index.isLt column)
  rw [firstRows]
  exact basis.coordinates_apply _

/-- A full coefficient vector with zero rejected entries is the same selected trajectory on its retained restriction.

The premise concerns exact support in the original coefficient ring. It
makes no inference from physical vanishing under a Gaussian reading.
-/
theorem horizon_restrict (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (rectangle : Rectangle bank.blocks bank.differenceInverses selection.word rows count)
    (coefficients : Vec K selection.fullWord.length)
    (supported : ∀ index : Fin selection.fullWord.length,
      selection.labels (selection.fullWord[index.val]'index.isLt) = false → coefficients index = 0) :
    Rectangular.apply (basis.horizon count) coefficients =
      Rectangular.apply (Rectangular.transpose rectangle.values) (coordinates.restrict coefficients) :=
  (congrArg (Rectangular.apply (basis.horizon count)) ((coordinates.support_iff coefficients).mpr supported).symm).trans
    (horizon_extend coordinates basis rectangle (coordinates.restrict coefficients))

/-- The actual selected startup boundary reads the same complete source trajectory on included coefficients. -/
theorem startup_extend (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (boundary : Recurrence.Boundary.Hermite bank selection.word rows count)
    (coefficients : Vec K selection.word.length) :
    Recurrence.boundary polynomial rows (Rectangular.apply (basis.horizon count) (coordinates.extend coefficients)) =
      Rectangular.apply boundary.boundary coefficients :=
  (congrArg (Recurrence.boundary polynomial rows)
    (horizon_extend coordinates basis boundary.readings coefficients)).trans (boundary.startup_eq coefficients)

/-- Original free selected startup coordinates give the same zero-left complete source trajectory and source rows. -/
theorem kernel_extend (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (boundary : Recurrence.Boundary.Hermite bank selection.word rows count)
    (companion : Dense.Companion polynomial)
    (free : Vec K (selection.word.length - boundary.normal.rank)) :
    Recurrence.boundary polynomial rows
        (Rectangular.apply (basis.horizon count) (coordinates.extend (boundary.normal.kernelVector free))) =
          vectorOfFn (fun _ => 0) ∧
      companion.Satisfies
        (Rectangular.apply (basis.horizon count) (coordinates.extend (boundary.normal.kernelVector free))) := by
  rw [horizon_extend coordinates basis boundary.readings]
  exact boundary.kernel_solution companion selection.admissible free

/-- Zero original startup rows characterize the same selected free normal-form coordinates inside the complete basis. -/
theorem kernel_extend_iff (coordinates : selection.Coordinates)
    (basis : Hermite bank.blocks bank.differenceInverses selection.fullWord)
    (boundary : Recurrence.Boundary.Hermite bank selection.word rows count)
    (coefficients : Vec K selection.word.length) :
    Recurrence.boundary polynomial rows (Rectangular.apply (basis.horizon count) (coordinates.extend coefficients)) =
      vectorOfFn (fun _ => 0) ↔
        boundary.normal.kernelVector (boundary.normal.kernelCoordinates coefficients) = coefficients := by
  rw [horizon_extend coordinates basis boundary.readings]
  exact boundary.kernel_iff coefficients

end Purelib.Polynomial.Recurrence.Mode.Hermite

end
